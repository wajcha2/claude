import RecompileExtensions

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

/-! The declarations formerly in this block were moved, with their
proofs unchanged, into RecompileExtensions before the three original
positive-node theorems. This module retains its public import path.
Source-order relocation: early section/evaluation proofs. No additional axiom is introduced. -/


/-!
## Construction-stage implementation register

This register records work still REQUIRED. It does not assert successful
elaboration, discharge of any proof, or agreement of every inherited API.
The final theorem remains conditional on the explicit input packages.
-/
namespace LeBrunSalamon.Construction.Manifest

set_option backward.isDefEq.respectTransparency false in
inductive Step where
  | fibreAndScalars | infinitesimalPoints | actualLineSubspaces | suitablePair
  | sourceAndHom | normalization | relativeTangent | fixedEnds | conicExtraction
  | finiteImage | normalizedImage | allSheets | transverseTest | purity
  | finiteEtaleRigidity | graphRecovery | assembly
  deriving DecidableEq, Repr, Fintype

def rank : Step → ℕ
  | .fibreAndScalars => 0 | .infinitesimalPoints => 1 | .actualLineSubspaces => 2
  | .suitablePair => 3 | .sourceAndHom => 4 | .normalization => 5
  | .relativeTangent => 6 | .fixedEnds => 7 | .conicExtraction => 8
  | .finiteImage => 9 | .normalizedImage => 10 | .allSheets => 11
  | .transverseTest => 12 | .purity => 13 | .finiteEtaleRigidity => 14
  | .graphRecovery => 15 | .assembly => 16

def prerequisites : Step → List Step
  | .fibreAndScalars => []
  | .infinitesimalPoints => [.fibreAndScalars]
  | .actualLineSubspaces => [.fibreAndScalars]
  | .suitablePair => [.actualLineSubspaces]
  | .sourceAndHom => [.infinitesimalPoints, .suitablePair]
  | .normalization => [.sourceAndHom, .actualLineSubspaces]
  | .relativeTangent => [.normalization, .infinitesimalPoints]
  | .fixedEnds => [.relativeTangent]
  | .conicExtraction => [.fixedEnds, .relativeTangent]
  | .finiteImage => [.fibreAndScalars]
  | .normalizedImage => [.finiteImage]
  | .allSheets => [.normalizedImage, .actualLineSubspaces]
  | .transverseTest => [.allSheets]
  | .purity => [.transverseTest]
  | .finiteEtaleRigidity => [.purity]
  | .graphRecovery => [.finiteEtaleRigidity, .finiteImage]
  | .assembly => [.conicExtraction, .graphRecovery]

theorem prerequisites_acyclic :
    ∀ s t : Step, t ∈ prerequisites s → rank t < rank s := by decide

structure Obligation where
  source : String
  entry : String
  exitCriterion : String

def obligation : Step → Obligation
  | .fibreAndScalars =>
    ⟨"intro:contact-sequence; sm:normalization", "CSections; Fiber; compositionPullback",
      "Canonical C-scalars, pullback comparisons, fibre exactness; compile all maps."⟩
  | .infinitesimalPoints =>
    ⟨"sm:relative-hom; sm:fixed-ends", "Infinitesimal.tangentToDual_bijective; Charts.Hom.differential",
      "All square-zero lifts correspond to actual point derivations; differentials are precomposition."⟩
  | .actualLineSubspaces =>
    ⟨"lines:positive; lines:free-cover", "Lines.positiveNodeSpace; Lines.CoveringFamily",
      "Endpoint-fixed node values are horizontal and isotropic; covering family is finite type."⟩
  | .suitablePair =>
    ⟨"lines:cone-addition; lines:suitable-pair", "Lines.suitablePair_exists",
      "Two actual free maps, complementary positive subspaces, actual df and nonzero Levi pairing."⟩
  | .sourceAndHom =>
    ⟨"sm:source; sm:relative-hom", "Smoothing.StandardSource; Smoothing.RelativeHom; Smoothing.Germ",
      "Represent the prescribed conic and full relative Hom functors on nonreduced tests too."⟩
  | .normalization =>
    ⟨"sm:normalization; sm:unconstrained-vanishing", "Normalization.normalizationRestriction_bijective",
      "Branch restriction is the actual isomorphism; H1 vanishing follows on the nodal fibre."⟩
  | .relativeTangent =>
    ⟨"sm:vertical-cokernel", "Normalization.RelativeTangentComparison",
      "Normalize by universal-evaluation square-zero lifts and commute with both endpoints."⟩
  | .fixedEnds =>
    ⟨"sm:shared-constant; sm:fixed-ends", "Smoothing.germ_noFixedEnds",
      "One common Laurent constant, global auxiliary fields, differentiated horizontality, nonzero Levi contradiction."⟩
  | .conicExtraction =>
    ⟨"sm:trivialization; sm:very-free", "Smoothing.germ_extracts_veryFreeConic",
      "Open evaluation locus meets nonzero smoothing parameter; base direction vanishes after actual trivialization."⟩
  | .finiteImage =>
    ⟨"des:descent, finite-image paragraph", "Descent.FiniteValueImage",
      "Use the actual graph in Tot(L boxtimes L), reduced integral image, and proper affine projection."⟩
  | .normalizedImage =>
    ⟨"des:base-open", "Descent.NormalizedImage; Descent.GoodOpen",
      "Finite birational normalization; a common dense BASE open; never assume a source-to-normalization map."⟩
  | .allSheets =>
    ⟨"des:component-section; des:all-sheets", "Descent.AllSheetsSplit; SheetAlgebra",
      "Both axis families and every generic sheet; scalar coordinate images do not require rational source points."⟩
  | .transverseTest =>
    ⟨"des:branch-model; des:pullback-germ", "Descent.RamifiedTest; SheetAlgebra.TransverseBranch",
      "Actual smooth normalized component and local-ring ramification; formal-to-analytic/local comparison proved."⟩
  | .purity =>
    ⟨"Stacks 0BMB; des:descent", "Descent.purity_over_contactSquare",
      "Source normal, base regular, finite quasi-finite map, equal local dimensions, all height-one generizations."⟩
  | .finiteEtaleRigidity =>
    ⟨"red:simply-connected; des:descent", "Descent.finiteEtale_contactSquare_trivial",
      "Fano simple connectedness and analytic covering comparison, with a nonempty connected source."⟩
  | .graphRecovery =>
    ⟨"Stacks 0AB1; des:descent", "Descent.finiteImage_graph_recovers_section",
      "Original image finite birational over the normal base; graph gives actual B; uniqueness by dominant pullback."⟩
  | .assembly =>
    ⟨"thm:main; thm:quaternionic", "Construction.leBrunSalamon_project",
      "Build all inputs; then inspect the entire axiom trace, including chosen foundational definitions."⟩

/-- Whole-monolith build flag; incremental module checks are recorded separately. -/
def compilerVerified : Bool := false

def geometricInputsDischarged : Bool := false

end LeBrunSalamon.Construction.Manifest

/-!
## Audit of this expansion

REPAIRS / QUALIFICATIONS
* Tangent spaces in the new deformation layer are submodules with genuine C-linear
  structure. Square-zero maps are normalized by 1 and epsilon, not arbitrary sets.
* The smooth line family is quasi-compact in the Zariski topology, so the smooth
  finite-type general-position arguments have the required finiteness hypothesis.
* All source equations and Hom universal properties range over nonreduced schemes.
* Suitable positive subspaces are actual node values of endpoint-fixed sections.
* The smoothing defect is exactly ONE. An explicit defect-two counterexample is
  retained in Regression; a dimension-only surrogate for evaluation is rejected.
* Descent uses the reduced image and its separate normalization, without a map from
  the original proper source to that normalization. No fibre-connectedness is assumed.
* Splitting tests cover the WHOLE generic finite pullback and BOTH axis families.
  Reducedness is explicit; dual numbers illustrate why residue fields alone do not suffice.
* Curve degrees are ranks of actual finite pushforwards. Ramification indices are
  maximal-ideal orders in the actual local-ring map at a CLOSED point.
* Normal extension needs Noetherian normal integral source charts and locally free
  target bundles. A cusp example records why normalization alone is not descent.
* The Kahler-to-dualizing map is first defined for the finite-type POLYNOMIAL node.
  Its completion/continuous-differential comparison is a separate geometric obligation.

WHAT IS AND IS NOT COMPLETED
The final route now assembles five smoothing slots and eight descent slots with
other existing manuscript inputs. Explicit assembly terms are provided; no entire
input package is constructed by sorry. Fundamental lemmas invoked by those terms
can still be admitted, and universal-property definitions may inherit sorryAx.
The proper stable-map/boundary construction, analytic comparison at branch points,
Picard reduction, integration/classification, and twistor/metric recovery remain
substantial obligations. The scalar and formal-ring modules do not prove them.

VALIDATION
The current verification reuses the exact checked baseline and compiles new
continuation modules in dependency order, as requested on 28 October 2026.
Exact source hashes, exit results and selected transitive axiom checks are
recorded in the checkpoint. Whole-monolith flags remain false unless that
separate build actually runs. Static inventories are not kernel checks.
Published input theorems remain explicit deferred obligations; priority is
now the manuscript's definitions and new geometric arguments, as recorded
in Project.linesAndSmoothingRemaining and the source-alignment plan.
-/

#check LeBrunSalamon.Construction.Smoothing.StandardSource
#check LeBrunSalamon.Construction.Smoothing.Germ
#check LeBrunSalamon.Construction.Normalization.normalizationRestriction
#check LeBrunSalamon.Construction.Normalization.RelativeTangentComparison
#check LeBrunSalamon.Construction.Descent.FiniteValueImage
#check LeBrunSalamon.Construction.Descent.RamificationIndex
#check LeBrunSalamon.Construction.Descent.Inputs
#check LeBrunSalamon.Construction.NodeDifferential.toDualizing
#check LeBrunSalamon.Construction.ProjectInputs
#check LeBrunSalamon.Construction.leBrunSalamon_project
#print axioms LeBrunSalamon.Construction.Smoothing.Inputs.assemble
#print axioms LeBrunSalamon.Construction.Descent.Inputs.assemble
#print axioms LeBrunSalamon.Construction.leBrunSalamon_project


/-!
# Proof work packages: manuscript labels, interfaces, and exit criteria

This is a dependency register, not a claim that any proof is discharged. The numbered order is
topological; edges are checked below. In particular, the downstream symmetric-jet theorem must NOT be used
to prove the upstream existence of a contact conic or of the full-family kernel.
-/
namespace LeBrunSalamon.Blueprint

set_option backward.isDefEq.respectTransparency false in
inductive Task where
  | foundations | curveModels | contactCalculus | picardReduction
  | lineGeometry | suitablePair | smoothing | homNeighborhood
  | stableBoundary | vectorExtension | contactDescent | fullFamilyIdentity
  | diagonalSymbol | symmetricJets | HamiltonianEvaluation | algebraicIntegration
  | homogeneousClassification | positiveTwistor | WolfRecovery | metricTransport | assembly
  deriving DecidableEq, Repr, Fintype

def rank : Task → ℕ
  | .foundations => 0 | .curveModels => 1 | .contactCalculus => 2
  | .picardReduction => 3 | .lineGeometry => 4 | .suitablePair => 5
  | .smoothing => 6 | .homNeighborhood => 7 | .stableBoundary => 8
  | .vectorExtension => 9 | .contactDescent => 10 | .fullFamilyIdentity => 11
  | .diagonalSymbol => 12 | .symmetricJets => 13 | .HamiltonianEvaluation => 14
  | .algebraicIntegration => 15 | .homogeneousClassification => 16
  | .positiveTwistor => 17 | .WolfRecovery => 18 | .metricTransport => 19 | .assembly => 20

def dependsOn : Task → List Task
  | .foundations => []
  | .curveModels => [.foundations]
  | .contactCalculus => [.foundations]
  | .picardReduction => [.foundations, .contactCalculus]
  | .lineGeometry => [.curveModels, .picardReduction]
  | .suitablePair => [.lineGeometry, .contactCalculus]
  | .smoothing => [.suitablePair, .curveModels]
  | .homNeighborhood => [.smoothing]
  | .stableBoundary => [.homNeighborhood, .curveModels]
  | .vectorExtension => [.stableBoundary, .contactCalculus]
  | .contactDescent => [.vectorExtension, .lineGeometry, .picardReduction]
  | .fullFamilyIdentity => [.contactDescent, .homNeighborhood]
  | .diagonalSymbol => [.fullFamilyIdentity]
  | .symmetricJets => [.foundations, .contactCalculus, .diagonalSymbol]
  | .HamiltonianEvaluation => [.symmetricJets, .contactCalculus]
  | .algebraicIntegration => [.HamiltonianEvaluation]
  | .homogeneousClassification => [.algebraicIntegration, .picardReduction]
  | .positiveTwistor => [.foundations, .curveModels, .contactCalculus]
  | .WolfRecovery => [.positiveTwistor, .homogeneousClassification]
  | .metricTransport => [.WolfRecovery]
  | .assembly => [.metricTransport]

theorem dependency_order :
    ∀ a b : Task, b ∈ dependsOn a → rank b < rank a := by decide

structure WorkPackage where
  source : String
  obligation : String
  acceptance : String

def package : Task → WorkPackage
  | .foundations =>
    ⟨"Stacks 01UM/01CF/01PR; intro:contact-sequence",
      "Compile the pinned file; prove canonical sheaf/tensor/differential comparisons and nonvacuous models.",
      "No data chosen without a universal property; normalization tests pass; every declaration elaborates."⟩
  | .curveModels =>
    ⟨"lines:standard-splitting; sm:source; ext:bivector",
      "Canonical P1 and O(d), splitting/cohomology, actual uv=s family and sourceBivector.",
      "Degree one is horizontal; degree two is not called a twistor fibre without the extra geometry."⟩
  | .contactCalculus =>
    ⟨"red:determinant; jet:hamiltonian",
      "Intrinsic Levi form, determinant identity, scalar-frame changes, global Hamiltonian correspondence.",
      "All local tests range over subopens; fields glue; complex-linearity is not O_X-linearity."⟩
  | .picardReduction =>
    ⟨"red:simply-connected; red:alternatives; hom:models",
      "Primitive/incidence/projective alternatives and NonprimitiveBranch.",
      "Projective case uses O(2), incidence uses O(1,1); no universal degree-one-line hypothesis."⟩
  | .lineGeometry =>
    ⟨"lines:fixed-degree; lines:positive; lines:free-cover",
      "Covering free contact lines, positive subbundles, and corrected Legendrian direction theorem.",
      "Use all components of the direction variety; do not assume each component spans."⟩
  | .suitablePair =>
    ⟨"lines:cone-addition; lines:suitable-pair",
      "Two actual free lines with complementary positive subspaces and nonzero Levi pairing.",
      "The n=1 case is handled separately; all chosen tangent directions are realizable."⟩
  | .smoothing =>
    ⟨"sm:relative-hom; sm:vertical-cokernel; sm:fixed-ends; sm:very-free",
      "Construction.Smoothing.Inputs: actual suitable pair, full relative-Hom germ, normalization diagram, fixed-end obstruction, conic extraction.",
      "Relative base motion contributes no spurious direction after trivializing the smooth-source family."⟩
  | .homNeighborhood =>
    ⟨"sm:full-germ; jet:value-velocity",
      "FullConicNeighborhood from the genuine represented Hom functor; open value--velocity image.",
      "Includes infinitesimal test schemes and an OPEN neighborhood, not only a dominant subfamily."⟩
  | .stableBoundary =>
    ⟨"ext:normal-products; ext:trees",
      "Normalized stable-map component and universal-curve square, integral and normal at boundary divisors.",
      "UNMARKED degree-two trees; entire generic fibres geometrically integral; no invented stack/scheme equivalence."⟩
  | .vectorExtension =>
    ⟨"ext:contact-order; ext:differential-order; ext:moving-pair",
      "Boundary thickness r, order-r vanishing, both vector lifts; Refinement.Boundary states the completed-node and height-one tests.",
      "Check all four component products; use normality to extend actual bundle-valued rational sections."⟩
  | .contactDescent =>
    ⟨"des:descent; des:all-sheets; des:branch-model",
      "Construction.Descent.Inputs: finite image, normalization/good open, all sheets, actual ramified test, purity, rigidity, graph recovery.",
      "Proper dominance alone is never treated as effective descent; embedded/vertical components are accounted for."⟩
  | .fullFamilyIdentity =>
    ⟨"ext:hom-vectors; ext:hom-identity; des:family",
      "Construct Refinement.CoveredMovingPair; prove descent and recover identity/symmetry with MovingPairInputs.assemble.",
      "Recover the entire Hom neighborhood and both moving source points, including the diagonal."⟩
  | .diagonalSymbol =>
    ⟨"jet:value-velocity; jet:diagonal; jet:second-symbol",
      "Refinement.DiagonalInputs: ordered value/first-symbol vanishing followed by the normalized Hessian.",
      "Undivided Hessian is 2 theta tensor theta; acceleration disappears only after first-symbol vanishing."⟩
  | .symmetricJets =>
    ⟨"jet:local-calculation; jet:criterion",
      "Refinement.Jets.Inputs: nonzero finite coefficients, actual contact Taylor data, and the contraction/jet diagram; assemble the criterion.",
      "Jet coordinates are normalized on ALL local functions; contractions are actual finite global sums; no inverse of the kernel tensor is assumed."⟩
  | .HamiltonianEvaluation =>
    ⟨"jet:hamiltonian; jet:criterion",
      "HamiltonianEvaluation realizes every tangent value from an ordinary first jet.",
      "Use the order-one Hamiltonian operator and extend a covector from the contact plane correctly."⟩
  | .algebraicIntegration =>
    ⟨"jet:transitive",
      "AlgebraicIntegration: complete global flows, open orbits, connectedness, algebraization and faithful action.",
      "Regular action morphism with identities on all test schemes; not an abstract-group permutation action."⟩
  | .homogeneousClassification =>
    ⟨"hom:adjoint; hom:moment; hom:hyperplane",
      "HomogeneousClassification via radical/Borel, finite moment map, highest weight, connected parabolic, KKS kernel.",
      "Produce AdjointContactPresentation with closed image, minimality, canonical contact distribution and polarization."⟩
  | .positiveTwistor =>
    ⟨"tw:normalization; tw:determinants; tw:fiber-splitting",
      "Salamon twistor construction, integrability, metric, real structure, Kodaira/GAGA and contact Fano algebraization.",
      "Actual analytic objects, not a point bijection. Twistor fibres have L-degree two and normal O(1)^(2n)."⟩
  | .WolfRecovery =>
    ⟨"twistor.tex: metric recovery; LeBrun Corollary 3.4",
      "PositiveTwistorReduction including the classified-model metric recovery map.",
      "Existence of a base homothety is proved; do not demand a given complex isomorphism preserve the real structure."⟩
  | .metricTransport =>
    ⟨"twistor.tex: final paragraph",
      "SymmetryImpliesParallel and HomothetyPreservesParallel for actual smooth metrics.",
      "Metric scale versus distance scale is distinguished; the Levi--Civita connection is preserved at constant scale."⟩
  | .assembly =>
    ⟨"thm:main; thm:quaternionic",
      "Construct Construction.ProjectInputs, apply Construction.leBrunSalamon_project, and replace the standalone admitted root.",
      "Final axiom trace has no sorryAx, including inside definitions; full semantic and example audit completed."⟩

/-- Enumeration coverage is not mathematical or compiler verification. -/
def documentedTaskCount : ℕ := Fintype.card Task

theorem documentedTaskCount_eq : documentedTaskCount = 21 := by decide

/-- Current integrated source has not been compiled; this is not a historical build flag. -/
def entireFileCompiled : Bool := false
def allProjectInputsProved : Bool := false

end LeBrunSalamon.Blueprint

/-!
# Project stages and source provenance

Stage 1 is complete as a definition/statement deliverable. Stage 2 foundationBuild has a verified
whole-file build at the pinned toolchain. Stage 3 linesAndSmoothing is in progress, with its algebraic
sublemmas proved and its geometric existence requirements still open. A completed compilation or
conditional assembly is not completion of the geometric proof.
-/

namespace LeBrunSalamon.Project

/-- Immutable manuscript snapshot used for the proof architecture. -/
def manuscriptCommit : String := "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"

def manuscriptDirectory : String :=
  "preprints/Contact-Fano-manifolds-and-the-LeBrun-Salamon-conjecture-September-23-2026/build/sections/"

/-- Exact mathlib snapshot used by the verified checkpoint builds. -/
def mathlibCommit : String := "116662aa4c1e9106ab5c609b3214b02f6e11a65a"

def leanToolchain : String := "leanprover/lean4:v4.36.0-rc1"

set_option backward.isDefEq.respectTransparency false in
/-- Stable project stages replace the purely chronological phase count. -/
inductive Stage where
  | declarationCore
  | foundationBuild
  | linesAndSmoothing
  | movingPairAndDescent
  | symmetricJets
  | homogeneityAndAdjoint
  | twistorRecovery
  | endToEndAudit
  deriving DecidableEq, Repr, Fintype

/-- Verification status distinguishes a written declaration layer
from an elaborated one, and both from a proof without admissions. -/
inductive Status where
  | declarationComplete
  | foundationComplete
  | inProgress
  | notStarted
  deriving DecidableEq, Repr

def stageNumber : Stage → ℕ
  | .declarationCore => 1
  | .foundationBuild => 2
  | .linesAndSmoothing => 3
  | .movingPairAndDescent => 4
  | .symmetricJets => 5
  | .homogeneityAndAdjoint => 6
  | .twistorRecovery => 7
  | .endToEndAudit => 8

def prerequisites : Stage → List Stage
  | .declarationCore => []
  | .foundationBuild => [.declarationCore]
  | .linesAndSmoothing => [.foundationBuild]
  | .movingPairAndDescent => [.foundationBuild, .linesAndSmoothing]
  | .symmetricJets => [.foundationBuild, .movingPairAndDescent]
  | .homogeneityAndAdjoint => [.foundationBuild, .symmetricJets]
  | .twistorRecovery => [.foundationBuild, .homogeneityAndAdjoint]
  | .endToEndAudit => [.twistorRecovery]

/-- The stage graph has no backward dependency or cycle. This checks
only the PLAN; it does not assert that the mathematics has been proved. -/
theorem prerequisites_strictly_earlier :
    ∀ s : Stage, ∀ t : Stage, t ∈ prerequisites s → stageNumber t < stageNumber s := by
  decide

def stageStatus : Stage → Status
  | .declarationCore => .declarationComplete
  | .foundationBuild => .foundationComplete
  | .linesAndSmoothing => .inProgress
  | _ => .notStarted

def firstOpenStage : Stage := .linesAndSmoothing

structure StageDescription where
  title : String
  deliverable : String
  exitCriterion : String
  sourceLabels : List String

/-- These are acceptance criteria, not retrospective progress claims. -/
def stageDescription : Stage → StageDescription
  | .declarationCore =>
      { title := "Source-pinned declaration core"
        deliverable := "Intrinsic normalized kernel, literal local coefficients, explicit construction cuts, conditional first-jet/Hamiltonian route."
        exitCriterion := "Definitions contain no final conclusions; source labels, signs, factorials, and dependency cuts are explicit. Build and proofs are separate stages."
        sourceLabels := ["jet:second-symbol", "jet:local-calculation", "jet:criterion"] }
  | .foundationBuild =>
      { title := "Compile and stabilize the intrinsic geometric foundation"
        deliverable := "A successful build of this single file at the pinned versions; canonical tensor/cotangent/contact operations; P1 and O(d); nonvacuous test examples."
        exitCriterion := "Zero elaboration errors, no sorry in data fields or silently arbitrary maps; each admitted proposition has a precise mathematical specification and provenance."
        sourceLabels := ["intro:contact-sequence", "red:determinant", "jet:symbol-bundles"] }
  | .linesAndSmoothing =>
      { title := "Picard reduction, suitable contact lines, and conics"
        deliverable := "Construct NonprimitiveBranch and PrimitiveSmoothing from actual model geometry and an actual nodal deformation."
        exitCriterion := "Standard branches handled; the normalization/evaluation cokernel and transverse smoothing direction proved; no dimension count substituted for existence."
        sourceLabels := ["red:alternatives", "lines:suitable-pair", "sm:vertical-cokernel", "sm:fixed-ends", "sm:very-free"] }
  | .movingPairAndDescent =>
      { title := "Full moving-pair construction and contact-value descent"
        deliverable := "Proper normalized stable-map source, extended vector lifts, genuine descent, and full local-family identity."
        exitCriterion := "Algebraic-space/scheme comparison justified; boundary poles cancelled; branching excluded; no generic pair or isolated conic substituted for a full Hom neighborhood."
        sourceLabels := ["sm:full-germ", "ext:moving-pair", "ext:normal-products", "ext:contact-order", "ext:differential-order", "des:descent", "des:family"] }
  | .symmetricJets =>
      { title := "Normalized diagonal symbol and symmetric-jet criterion"
        deliverable := "Construct ConicToNormalizedKernel; prove NormalizedContactKernel.separatesFirstJets and the global Hamiltonian correspondence."
        exitCriterion := "Open velocity locus, coefficient normalization, symmetry-forced cubic, actual contractions and first-jet surjectivity all proved."
        sourceLabels := ["jet:value-velocity", "jet:diagonal", "jet:local-calculation", "jet:hamiltonian", "jet:criterion"] }
  | .homogeneityAndAdjoint =>
      { title := "Global algebraic action and adjoint contact variety"
        deliverable := "Integrate global fields, build the effective connected algebraic group and its simple Lie algebra, identify the actual adjoint variety and polarization."
        exitCriterion := "A contact isomorphism of schemes with actual differential; not merely a set orbit, a group label, or a supplied tangent action."
        sourceLabels := ["jet:transitive", "hom:adjoint", "hom:models", "thm:main"] }
  | .twistorRecovery =>
      { title := "Twistor construction and metric recovery"
        deliverable := "Positive twistor geometry, algebraization, Wolf model, normalized metric uniqueness, and parallel curvature of the original manifold."
        exitCriterion := "Actual manifolds, metrics, complex/real structures and comparison maps; scalar normalization and simple connectedness proved rather than inferred from labels."
        sourceLabels := ["tw:normalization", "tw:fiber-splitting", "thm:quaternionic"] }
  | .endToEndAudit =>
      { title := "Close the manuscript proof and audit all dependencies"
        deliverable := "A main proof assembled only from the previous stages, with a complete axiom trace and independent semantic review."
        exitCriterion := "No sorryAx in the final theorem or its definitions; no admitted main target used indirectly; examples and statement equivalence checked."
        sourceLabels := ["thm:main", "thm:quaternionic"] }

/-- A source locator names an actual manuscript file and TeX label.
The label is stable across page-number changes. -/
structure SourceLocator where
  file : String
  label : String
  blob : String
  role : String

/-- Critical source-to-code map. Multiple labels may share a source
file, but no statement is attributed just to a paper title. -/
def coreSources : List SourceLocator :=
  [ { file := "reduction.tex", label := "red:alternatives"
      blob := "2a84b9097159eaed26ac4dc625116183e30e1d9a"
      role := "NonprimitiveBranch: standard incidence/projective alternatives." },
    { file := "lines.tex", label := "lines:suitable-pair"
      blob := "5066b53e73f46b8435dd71e31a77ffdb6effdaad"
      role := "Actual free contact lines with complementary positive tangent subspaces." },
    { file := "smoothing.tex", label := "sm:very-free"
      blob := "a5fd8e88f5233ea0e4bcade993432376b4503748"
      role := "VeryFreeContactConic and PrimitiveSmoothing." },
    { file := "smoothing.tex", label := "sm:full-germ"
      blob := "a5fd8e88f5233ea0e4bcade993432376b4503748"
      role := "Full Hom-neighborhood compatibility, not a selected subfamily." },
    { file := "extension.tex", label := "ext:moving-pair"
      blob := "5c21ba07f2812adda53eb4de3c5b04f65377b247"
      role := "Proper algebraic-space source and both extended vector lifts." },
    { file := "descent.tex", label := "des:descent"
      blob := "75cd8faef074b298b4b335197e34f304f71b5c17"
      role := "Existence of descent via contact-line tests, not generic proper descent." },
    { file := "descent.tex", label := "des:family"
      blob := "75cd8faef074b298b4b335197e34f304f71b5c17"
      role := "Symmetry and the full moving-source-pair identity." },
    { file := "jets.tex", label := "jet:diagonal"
      blob := "9b5068fca564cdab2a92336d28e52cdd90625826"
      role := "NormalizedContactKernel: actual I^2 vanishing and Hessian = 2 theta tensor theta." },
    { file := "jets.tex", label := "jet:local-calculation"
      blob := "9b5068fca564cdab2a92336d28e52cdd90625826"
      role := "Literal cubic/first-slot coefficients in LocalJet." },
    { file := "jets.tex", label := "jet:criterion"
      blob := "9b5068fca564cdab2a92336d28e52cdd90625826"
      role := "NormalizedContactKernel.separatesFirstJets." },
    { file := "jets.tex", label := "jet:hamiltonian"
      blob := "9b5068fca564cdab2a92336d28e52cdd90625826"
      role := "Intrinsic first-jet-to-global-Hamiltonian comparison." },
    { file := "homogeneous.tex", label := "hom:adjoint"
      blob := "ee4f67428b234626e413de0465682ef0375258bc"
      role := "Later integration and contact-isomorphism theorem; not supplied by current core." },
    { file := "twistor.tex", label := "tw:fiber-splitting"
      blob := "b44af9a040c7ddfc91c5f3fcc0131e2b26252ddd"
      role := "Later analytic/algebraic bridge, with contact degree two on twistor fibres." } ]

/-- A compact registry of the Stage 1 declarations retained and elaborated
in the Stage 2 build. Strings are metadata; the compiler log is the evidence. -/
def stageOneDeliverables : List String :=
  [ "Core.AffineLineFrame",
    "Core.ExternalExpansion",
    "Core.ExternalExpansion.secondSlotSecond",
    "Core.HasNormalizedContactSymbol",
    "Core.NormalizedContactKernel",
    "Core.LocalJet.IsProjectiveKernelDirection",
    "Core.LocalJet.projectiveKernelDirection_zero",
    "Core.VeryFreeContactConic",
    "Core.ManuscriptCoreInputs",
    "Core.manuscriptCore_firstJets",
    "Core.manuscriptCore_HamiltonianSpanning" ]

/-- Recorded build status; see the source hash and full log in the latest checkpoint bundle. -/
def compilationVerified : Bool := false

/-- Completed foundation work, with the exact remaining obligations in the external audit. -/
def foundationBuildScope : String :=
  "Reuse the exact verified baseline; check new continuation modules in dependency order and record their source hashes, compiler results and transitive audit separately. Original predicates and theorem statements are retained. Published inputs remain explicit deferred obligations; priority follows the manuscript-specific constructions."

/-- Completed Stage 3 algebra is distinct from the required geometric existence witnesses. -/
def linesAndSmoothingScope : String :=
  "Checked splitting arithmetic; actual matching-evaluation cokernel equivalence; tangent/dual-number equivalence; polynomial and completed first-order node algebra; defect-one endpoint-surjectivity argument; explicit geometric and sheaf-coherence deductions."

/-- These are remaining proof obligations, not added hypotheses of the final target. -/
def linesAndSmoothingRemaining : List String :=
  [ "Priority: define the actual tangent-direction variety and its component cones; prove lines:positive, lines:cone-addition and lines:suitable-pair, allowing disconnected directions and the n=1 case.",
    "Construct the prescribed nodal source and normalization/evaluation comparisons; use the full relative Hom functor and actual square-zero differentials (sm:source, sm:normalization, sm:vertical-cokernel).",
    "Connect the shared-constant node calculation to global auxiliary fields and differentiated horizontality; prove germ_noFixedEnds and extract the very free conic with its full Hom neighborhood (sm:fixed-ends, sm:very-free, sm:full-germ).",
    "Continue in manuscript order through moving-pair extension, all-sheet descent, ordered diagonal symbols and the symmetry-forced cubic/first-jet criterion; retain both moving source points and genuine algebraic-space comparisons.",
    "Defer proofs of cited published inputs: P1 line-bundle classification and Birkhoff--Grothendieck, Kebekus/Buczynski contact-line results, relative-Hom representability/smoothness, purity and twistor/classification foundations. Keep their exact hypotheses, citations and admissions explicit; the manuscript's own new geometric deductions remain priority proof obligations." ]

/-- Completed: the actual Proj atlas and the rational point-ideal rank theorem. -/
def projectiveLineAtlasAndPointIdealConstructed : Bool := true

/-- O(d) comparison, line-bundle classification, sheaf cohomology and splitting remain open. -/
def projectiveLineBundleTheoryComplete : Bool := false

/-- Conditional assembly does not construct NonprimitiveBranch or PrimitiveSmoothing. -/
def linesAndSmoothingGeometricInputsConstructed : Bool := false

/-- The compiled foundation does not discharge the remaining geometric proof stages. -/
def geometricProofsComplete : Bool := false

end LeBrunSalamon.Project

#check LeBrunSalamon.Core.NormalizedContactKernel
#check LeBrunSalamon.Core.ManuscriptCoreInputs
#check LeBrunSalamon.Core.manuscriptCore_firstJets
/- This exact query follows its relocated declaration in LSHamiltonianJets. -/
#print axioms LeBrunSalamon.Core.LocalJet.projectiveKernelDirection_zero
#print axioms LeBrunSalamon.Core.NormalizedContactKernel.separatesFirstJets
#print axioms LeBrunSalamon.Core.manuscriptCore_firstJets

/- Original root query relocated to LSCompletedTargets with its declaration. -/
#check LeBrunSalamon.PhaseTwentyFive.cotangentSheaf
#check LeBrunSalamon.PhaseTwentySeven.ContactFanoManifold
#check LeBrunSalamon.PhaseTwentyEight.externalSquareLine
#check LeBrunSalamon.PhaseThirty.cotangentMap
#check LeBrunSalamon.PhaseThirtyTwo.projectiveTwist
#check LeBrunSalamon.PhaseThirtyTwo.birkhoffGrothendieck
#check LeBrunSalamon.PhaseThirtyFive.veryFreeContactConic_actualSplitting
/- Original root query relocated to LSCompletedTargets with its declaration. -/
#print axioms LeBrunSalamon.PhaseTwentyFive.cotangentSheaf
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveTwist

#check LeBrunSalamon.Skeleton.AlgebraicInputs
#check LeBrunSalamon.Skeleton.RiemannianInputs
#check LeBrunSalamon.Skeleton.ProjectInputs
#check LeBrunSalamon.Skeleton.canonicalProjectiveLine
#check LeBrunSalamon.Skeleton.canonicalMarkedPoint
#check LeBrunSalamon.Skeleton.ContactIso
#check LeBrunSalamon.Skeleton.FullFamilyKernel
#check LeBrunSalamon.Skeleton.AdjointContactPresentation
#check LeBrunSalamon.Skeleton.TwistorReductionOutput
#check LeBrunSalamon.Skeleton.project_symmetricHomothety
#check LeBrunSalamon.Skeleton.leBrunSalamon_project
#check LeBrunSalamon.Skeleton.leBrunSalamon_fromProjectInputs
#print axioms LeBrunSalamon.Skeleton.differentialOver
#print axioms LeBrunSalamon.Skeleton.project_contactFanoClassification
#print axioms LeBrunSalamon.Skeleton.leBrunSalamon_project
#print axioms LeBrunSalamon.Skeleton.leBrunSalamon_fromProjectInputs
#print axioms LeBrunSalamon.Blueprint.dependency_order

/-!
## Consolidated audit -- 27 October 2026, Stage 3 algebraic checkpoint

TRUST: The historical v20 statement/specification baseline was compiled at the pinned versions.
The exact verification status of this continuation is recorded with its source hash.
Definitions chosen from admitted existence theorems still depend on sorryAx.
The assembly uses supplied inputs, not the admitted global criterion or any legacy
*_target. No input-package constructor is admitted. The inherited definitions still require full review.

NEW: Pointed affine line frames; actual local evaluation and point derivations; fat-point restrictions;
jet coordinates normalized on ALL local functions; finite coefficient vectors and actual global
contractions; contact covector and exterior-form normalizations; three separate symmetric-jet proof
inputs; frame covariance with the mandatory dq term. Any finite external expansion works, without assuming
its factors independent or the two-point tensor nondegenerate.

The old immersiveKernel_separatesFirstJets proof is replaced by an explicit injective-map/dual-map
argument using mathlib. This proof now compiles and has no sorryAx in its axiom trace.
No finite-dimensionality of the section space is used.

AUDIT BOUNDARIES: Completed-node algebra, pole bounds and height-one extension are not geometric
identifications. Scheme covers still need justified descent of the full-family comparison.
TaylorRealization is the output of the actual local coefficient calculation, not an assumed immersion. Its
theta and exterior form are normalized on local tangent fields. Local jet-coordinate existence is a
foundational obligation; it does not assert global generation of jets.

VALIDATION: The latest checkpoint states whether whole-file verification has run and records
the observed component or integrated axiom traces, together with the complete lexical admission inventory
and a semantic review of every remaining hole inside definitions. The nonvacuous
contact model is affine A3; it does not construct a proper contact-Fano manifold.
Stage 3, linesAndSmoothing, remains the first open stage, with status inProgress.
Its algebraic sublemmas now include actual cokernel equivalences and the completed
first-order node, while the geometric existence requirements are unchanged.
The complete conjecture still has not been formally proved.
-/

#check LeBrunSalamon.Refinement.CoveredMovingPair
#check LeBrunSalamon.Refinement.MovingPairInputs
#check LeBrunSalamon.Refinement.DiagonalInputs
#check LeBrunSalamon.Refinement.Boundary.FormalNode
#check LeBrunSalamon.Refinement.leBrunSalamon_project
#print axioms LeBrunSalamon.Refinement.MovingPairInputs.assemble
#print axioms LeBrunSalamon.Refinement.DiagonalInputs.assemble
#print axioms LeBrunSalamon.Refinement.leBrunSalamon_project


#check LeBrunSalamon.Refinement.Jets.PointFrame
#check LeBrunSalamon.Refinement.Jets.PointFrame.jetCoordinates
#check LeBrunSalamon.Refinement.Jets.TaylorRealization
#check LeBrunSalamon.Refinement.Jets.Inputs
#print axioms LeBrunSalamon.PhaseTwentyTwo.immersiveKernel_separatesFirstJets
#print axioms LeBrunSalamon.Refinement.Jets.Inputs.assemble

end -- noncomputable section



set_option autoImplicit false

/-!
# Foundation-build axiom audit

Compile this file against the compiled integrated module with the pinned
toolchain. The `#print axioms` commands inspect transitive dependencies,
including dependencies in declaration types. The comments below are expected
classifications to verify against the emitted compiler log, not proof claims.

`propext`, `Classical.choice`, and `Quot.sound` are ordinary Lean axioms used
by mathlib. A declaration whose output contains `sorryAx` is still conditional
on one or more admitted statements. Absence of a literal `sorry` in its own
body does not establish absence of inherited admissions.
-/

/-! ## A. Completed constructions and proofs: expect no `sorryAx`. -/

-- Genuine affine contact form dz - x dy on A³, using the actual predicate.
#print axioms LeBrunSalamon.FoundationExamples.AffineThreeSpace.theta
#print axioms LeBrunSalamon.FoundationExamples.AffineThreeSpace.kernel_decomposition
#print axioms LeBrunSalamon.FoundationExamples.AffineThreeSpace.leviPair_is_bracket
#print axioms LeBrunSalamon.FoundationExamples.AffineThreeSpace.levi_basis_value
#print axioms LeBrunSalamon.FoundationExamples.AffineThreeSpace.leviPair_perfect
#print axioms LeBrunSalamon.FoundationExamples.AffineThreeSpace.theta_isAffineContactForm
#print axioms LeBrunSalamon.FoundationExamples.AffineThreeSpace.theta_nonzero

-- Concrete sheafification and functorial operations on specified sheaf maps.
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorSheaf
#print axioms LeBrunSalamon.PhaseTwentyFive.sheafHom_naturality
#print axioms LeBrunSalamon.PhaseTwentyFive.SheafBilinearMap.postcompose
#print axioms LeBrunSalamon.PhaseTwentyFive.SheafBilinearMap.precompose
#print axioms LeBrunSalamon.PhaseTwentyFive.RelativeSheafDerivation.postcompose
#print axioms LeBrunSalamon.PhaseTwentySix.SheafAlternatingMap.postcompose
#print axioms LeBrunSalamon.PhaseTwentySix.SheafSymmetricMap.postcompose
#print axioms LeBrunSalamon.PhaseTwentyEight.unitPullbackMap
#print axioms LeBrunSalamon.PhaseTwentyEight.unitPullbackMap_isIso
#print axioms LeBrunSalamon.PhaseTwentyEight.unitPullbackIso
#print axioms LeBrunSalamon.PhaseTwentyEight.sectionValue_bijective

-- The actual coefficient identification for the Proj model of P¹.
#print axioms LeBrunSalamon.Skeleton.constantsToDegreeZero
#print axioms LeBrunSalamon.Skeleton.constantsToDegreeZero_bijective
#print axioms LeBrunSalamon.Skeleton.zeroDegreeSchemeIso
#print axioms LeBrunSalamon.Skeleton.canonicalProjectiveLine
#print axioms LeBrunSalamon.Skeleton.canonicalProjectiveLine_structureMap

-- Finite-dimensional jet linear algebra, with no finite-dimensional section-space assumption.
#print axioms LeBrunSalamon.PhaseNineteen.contactHamiltonianValue_unique
#print axioms LeBrunSalamon.PhaseNineteen.contactQuadratic_nonzero
#print axioms LeBrunSalamon.PhaseTwentyTwo.immersiveKernel_separatesFirstJets
#print axioms LeBrunSalamon.PhaseTwentyTwo.separatingKernel_isImmersive

-- Quotient maps between the actual powers-of-maximal-ideal jet algebras.
#print axioms LeBrunSalamon.PhaseThirtyOne.jetTruncation
#print axioms LeBrunSalamon.PhaseThirtyOne.jetTruncation_surjective
#print axioms LeBrunSalamon.PhaseThirtyOne.jetTruncation_comp
#print axioms LeBrunSalamon.PhaseThirtyOne.affineJet_eq_iff
#print axioms LeBrunSalamon.PhaseThirtyOne.affineJet_zero_iff
#print axioms LeBrunSalamon.PhaseThirtyOne.sameJet_implies_sameLowerJet

-- Genuine dual numbers, point derivations, and their explicit maps.
#print axioms LeBrunSalamon.Construction.Infinitesimal.tangentSpace
#print axioms LeBrunSalamon.Construction.Infinitesimal.tangentMap
#print axioms LeBrunSalamon.Construction.Infinitesimal.epsilon_square
#print axioms LeBrunSalamon.Construction.Infinitesimal.epsilon_ne_zero
#print axioms LeBrunSalamon.Construction.Infinitesimal.dual_normalForm
#print axioms LeBrunSalamon.Construction.Infinitesimal.tangentToDual
#print axioms LeBrunSalamon.Construction.Infinitesimal.tangentToDual_residue
#print axioms LeBrunSalamon.Construction.Infinitesimal.tangentToDual_natural
#print axioms LeBrunSalamon.Construction.Infinitesimal.scaleDual
#print axioms LeBrunSalamon.Construction.Infinitesimal.tangentToDual_smul

-- Polynomial node: actual logarithmic derivation and Kähler differential map.
#print axioms LeBrunSalamon.Construction.NodeDifferential.polynomialLogDerivation_equation
#print axioms LeBrunSalamon.Construction.NodeDifferential.explicitLogDerivation
#print axioms LeBrunSalamon.Construction.NodeDifferential.logDerivation_existsUnique
#print axioms LeBrunSalamon.Construction.NodeDifferential.toDualizing
#print axioms LeBrunSalamon.Construction.NodeDifferential.toDualizing_du
#print axioms LeBrunSalamon.Construction.NodeDifferential.toDualizing_dv
#print axioms LeBrunSalamon.Construction.NodeDifferential.generators_surjective

-- Counterexamples that prevent invalid geometric inference steps.
#print axioms LeBrunSalamon.Construction.Regression.defectTwo_not_surjective
#print axioms LeBrunSalamon.Construction.Regression.squareCover_has_nondescending_function
#print axioms LeBrunSalamon.Construction.Regression.normalization_function_not_on_cusp
#print axioms LeBrunSalamon.Construction.Regression.equal_dimensions_do_not_force_evaluation

/-! ## B. Completed local proofs with inherited foundation admissions.

These declarations have proved bodies, but their types or implementations
use the chosen tensor/cotangent/internal-Hom presentations, the existence of
the tangent bracket, or admitted compatibility theorems. Expect `sorryAx`.
-/

#print axioms LeBrunSalamon.PhaseTwentyFive.tangentBracket_spec
#print axioms LeBrunSalamon.PhaseTwentyFive.tangentBracket_add_left
#print axioms LeBrunSalamon.PhaseTwentyFive.tangentBracket_add_right
#print axioms LeBrunSalamon.PhaseTwentySeven.intrinsicLeviPair
#print axioms LeBrunSalamon.PhaseThirty.pulledFunctionDifferential
#print axioms LeBrunSalamon.PhaseThirty.relativeDifferentialOverComposite

/-! ## C. Selected explicit foundation obligations: expect `sorryAx`.

These samples show the precise boundary of stage 2. The whole-file admission
inventory, rather than this selected audit, is the complete remaining-work
register. O(d), the marked projective point, and the node's geometric
comparison remain dependent on the listed mathematical obligations.
-/

#print axioms LeBrunSalamon.PhaseTwentyFive.tensorSheafPresentation_exists
#print axioms LeBrunSalamon.PhaseTwentyFive.internalHomPresentation_exists
#print axioms LeBrunSalamon.PhaseTwentyFive.cotangentPresentation_exists
#print axioms LeBrunSalamon.PhaseTwentyFive.tangentBracket_existsUnique
#print axioms LeBrunSalamon.PhaseTwentySix.exteriorPresentation_exists
#print axioms LeBrunSalamon.PhaseTwentySix.symmetricPresentation_exists
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectivePointIdeal_rankOne
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveTwist
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveLineBundle_classification
#print axioms LeBrunSalamon.Skeleton.projectiveCoordinates_exists
#print axioms LeBrunSalamon.Skeleton.canonicalMarkedPoint
#print axioms LeBrunSalamon.Construction.NodeDifferential.generators_kernel
#print axioms LeBrunSalamon.Construction.NodeDifferential.toDualizing_range

/-! ## D. Project boundary: input hypotheses and transitive admissions.

The preferred root is an assembly theorem with an explicit ProjectInputs
argument. It does not constitute a proof that those geometric inputs exist.
The original unconditional target is declared after the constructed inputs
in LSCompletedTargets. Inspect its signature and native dependency evidence there.
-/

#check LeBrunSalamon.Construction.AlgebraicInputs
#check LeBrunSalamon.Construction.ProjectInputs
#check LeBrunSalamon.Construction.leBrunSalamon_project
#print axioms LeBrunSalamon.Construction.project_contactFanoClassification
#print axioms LeBrunSalamon.Construction.leBrunSalamon_project
/- Original root query relocated to LSCompletedTargets with its declaration. -/
/- Original root query relocated to LSCompletedTargets with its declaration. -/

/-! ## Stage 3 checkpoint: additional transitive axiom checks. -/

#print axioms LeBrunSalamon.Construction.Charts.Hom.differential
#print axioms LeBrunSalamon.Construction.Charts.Hom.evaluation_onFunctions
#print axioms LeBrunSalamon.Construction.Charts.Hom.onFunctions
#print axioms LeBrunSalamon.Construction.Charts.PointedAffine.evaluation
#print axioms LeBrunSalamon.Construction.Infinitesimal.dual_normalForm_reconstruct
#print axioms LeBrunSalamon.Construction.Infinitesimal.linearCoefficient_add
#print axioms LeBrunSalamon.Construction.Infinitesimal.linearCoefficient_algebraMap
#print axioms LeBrunSalamon.Construction.Infinitesimal.linearCoefficient_mul
#print axioms LeBrunSalamon.Construction.Infinitesimal.linearCoefficient_smul
#print axioms LeBrunSalamon.Construction.Infinitesimal.tangentToDual_bijective
#print axioms LeBrunSalamon.Construction.Infinitesimal.tangent_kills_maximalSquare
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.FirstOrderNode
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.NodeSeriesRing
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.coordinate_ne_zero
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.epsilon
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.epsilon_annihilator
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.epsilon_nonzero
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.epsilon_square
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.firstOrderIdeal
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.sharedConstant
#print axioms LeBrunSalamon.Construction.Smoothing.FormalNode.vector_sharedConstant
#print axioms LeBrunSalamon.Construction.Smoothing.baseLift_not_vertical
#print axioms LeBrunSalamon.Construction.Smoothing.endpoint_surjective_of_defect_one
#print axioms LeBrunSalamon.Construction.Smoothing.noFixedEnds_iff_kernel
#print axioms LeBrunSalamon.Construction.Smoothing.scalarPoint_overC
#print axioms LeBrunSalamon.Construction.complexConstants
#print axioms LeBrunSalamon.Construction.complexConstants_apply_top
#print axioms LeBrunSalamon.Construction.complexConstants_naturality
#print axioms LeBrunSalamon.Construction.compositionPullback_sections
#print axioms LeBrunSalamon.Construction.evaluateSection
#print axioms LeBrunSalamon.Construction.fiberComposition_bijective
#print axioms LeBrunSalamon.Construction.onCSections
#print axioms LeBrunSalamon.Construction.onCSections_bijective_of_iso
#print axioms LeBrunSalamon.Construction.pullCSectionsAlong
#print axioms LeBrunSalamon.Construction.pullSection_comp
#print axioms LeBrunSalamon.Construction.pullbackComp_homEquiv
#print axioms LeBrunSalamon.Construction.structurePushforwardMap_comp
#print axioms LeBrunSalamon.Construction.unitPullbackIso_comp
#print axioms LeBrunSalamon.Construction.unitPullbackMap_comp
#print axioms LeBrunSalamon.Construction.unitPullbackMap_comp_hom
#print axioms LeBrunSalamon.PhaseEighteen.quasiLineProfile_cohomology
#print axioms LeBrunSalamon.PhaseThirtyFour.firstOrderNode_sharedConstant
#print axioms LeBrunSalamon.PhaseThirtyFour.firstOrderParameter_annihilator
#print axioms LeBrunSalamon.PhaseThirtyFour.firstOrderParameter_nonzero
#print axioms LeBrunSalamon.PhaseThirtyFour.firstOrderParameter_square
#print axioms LeBrunSalamon.PhaseThirtyFour.matchingEndpoint_cokernel
#print axioms LeBrunSalamon.PhaseThirtyFour.matchingEndpoint_defectDimension
#print axioms LeBrunSalamon.PhaseThirtyFour.matchingEndpoint_surjective_iff
#print axioms LeBrunSalamon.PhaseThirtyFour.normalization_sectionDimension
#print axioms LeBrunSalamon.PhaseThirtyThree.dualProfile_degree
#print axioms LeBrunSalamon.PhaseThirtyThree.fixedTwoPointParameterization_kernelDimension
#print axioms LeBrunSalamon.PhaseThirtyThree.freeContactLine_positiveDegreeSum
#print axioms LeBrunSalamon.PhaseThirtyThree.freeProfile_hOne_zero
#print axioms LeBrunSalamon.PhaseThirtyThree.freeProfile_hZero
#print axioms LeBrunSalamon.PhaseThirtyThree.minimumVeryFreeDegree_forces_allOnes
#print axioms LeBrunSalamon.PhaseThirtyThree.nextVeryFreeDegree_forces_quasiLine
#print axioms LeBrunSalamon.PhaseThirtyThree.profile_hOne_zero_iff
#print axioms LeBrunSalamon.PhaseThirtyThree.profile_hZero_zero_iff
#print axioms LeBrunSalamon.PhaseThirtyThree.profile_riemannRoch
#print axioms LeBrunSalamon.PhaseThirtyThree.profile_serreDuality_number
#print axioms LeBrunSalamon.PhaseThirtyThree.profile_twoPointEuler
#print axioms LeBrunSalamon.PhaseThirtyThree.profile_twoPointObstructions_zero_iff
#print axioms LeBrunSalamon.PhaseThirtyThree.quasiLineProfile_totalDegree
#print axioms LeBrunSalamon.PhaseThirtyThree.quasiLine_parametrizedEvaluationRelativeDimension
#print axioms LeBrunSalamon.PhaseThirtyThree.quasiLine_unparameterizedEvaluationRelativeDimension
#print axioms LeBrunSalamon.PhaseThirtyThree.twistProfile_degree
#print axioms LeBrunSalamon.PhaseThirtyThree.twoMarkedDimension_agrees
#print axioms LeBrunSalamon.PhaseThirtyThree.veryFreeProfile_degreeBound
#print axioms LeBrunSalamon.PhaseThirtyThree.veryFree_with_tangent_degreeBound
#print axioms LeBrunSalamon.PhaseTwenty.standardContactLineProfile_cohomology
#print axioms LeBrunSalamon.PhaseTwenty.standardContactLineProfile_degree
#print axioms LeBrunSalamon.PhaseTwenty.standardContactLineProfile_positive_rank
#print axioms LeBrunSalamon.PhaseTwenty.suitablePair_intersection_trivial
#print axioms LeBrunSalamon.PhaseTwenty.suitablePair_velocities_nonzero
#print axioms LeBrunSalamon.PhaseTwentyEight.globalSectionFamilyEquiv
#print axioms LeBrunSalamon.PhaseTwentyEight.pullSectionValue_smul
#print axioms LeBrunSalamon.PhaseTwentyEight.pullSection_adjoint
#print axioms LeBrunSalamon.PhaseTwentyEight.pullSection_naturality
#print axioms LeBrunSalamon.PhaseTwentyEight.pullSection_value
#print axioms LeBrunSalamon.PhaseTwentyEight.sectionFromValue_spec
#print axioms LeBrunSalamon.PhaseTwentyEight.structurePushforwardMap_one
#print axioms LeBrunSalamon.PhaseTwentyEight.unitPullbackMap_adjoint
#print axioms LeBrunSalamon.PhaseTwentyEight.unitPullbackMap_pullSection
#print axioms LeBrunSalamon.PhaseTwentyFive.sheafBilinearMap_ext
#print axioms LeBrunSalamon.Stage3Lines.card_fin_filter_lt
#print axioms LeBrunSalamon.Stage3Lines.sum_fin_ite_lt
#print axioms LeBrunSalamon.Stage3Lines.sum_standardLineProfile
#print axioms LeBrunSalamon.Construction.Lines.contactPlane_dimension
#print axioms LeBrunSalamon.Construction.Lines.leviFiberValue_smul_smul
#print axioms LeBrunSalamon.Construction.Lines.nonzeroLeviPair_rescale
#print axioms LeBrunSalamon.Construction.Lines.suitablePair_complementary
#print axioms LeBrunSalamon.Construction.Lines.suitablePair_positive_dimensions
#print axioms LeBrunSalamon.Construction.Lines.zero_ne_infinity
#print axioms LeBrunSalamon.Construction.Normalization.branches_meet
#print axioms LeBrunSalamon.Construction.Normalization.centralMap_left
#print axioms LeBrunSalamon.Construction.Normalization.centralMap_over
#print axioms LeBrunSalamon.Construction.Normalization.centralMap_right
#print axioms LeBrunSalamon.Construction.Normalization.contactNormal_dimension
#print axioms LeBrunSalamon.Construction.Normalization.endpointSectionsMap_matching
#print axioms LeBrunSalamon.Construction.Normalization.endpointSections_cokernel
#print axioms LeBrunSalamon.Construction.Normalization.normalizationRestriction
#print axioms LeBrunSalamon.Construction.Normalization.pullCSections
#print axioms LeBrunSalamon.Construction.Normalization.relativeTangentComparison_defectOne
#print axioms LeBrunSalamon.PhaseThirtyTwo.freeBundle_firstCohomology_vanishes
#print axioms LeBrunSalamon.PhaseThirtyTwo.intrinsicContactConic_nonzeroVelocity_isIso
#print axioms LeBrunSalamon.PhaseThirtyTwo.intrinsicContactLine_velocity_zero
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveLineDegree_iso
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveLineDegree_power
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveLineDegree_spec
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveLineDegree_tensor
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveTwist_degree
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveTwist_iso_iff
#print axioms LeBrunSalamon.PhaseTwentyFive.currySheaf_evaluate
#print axioms LeBrunSalamon.PhaseTwentyFive.differentialLift_spec
#print axioms LeBrunSalamon.PhaseTwentyFive.differentialLift_unique
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorIso
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorLift_pair
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorMap_apply
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorMap_comp
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorMap_id
#print axioms LeBrunSalamon.PhaseThirtyTwo.birkhoffGrothendieck
#print axioms LeBrunSalamon.PhaseThirtyTwo.primitiveContactFano_hasFreeContactLine
/- The exact suitablePair_exists diagnostic follows its relocated
declaration in LSSuitablePair. -/
#print axioms LeBrunSalamon.Construction.Smoothing.germ_exists
/- The germ_extracts_veryFreeConic diagnostic follows its exact relocated
declaration in LSNodalConic. -/
#print axioms LeBrunSalamon.Construction.Normalization.normalizationRestriction_bijective
/- This exact query follows its relocated declaration in LSNodalTangent. -/

/-! P1 CHECKPOINT TRANSITIVE AUDIT: no admissions allowed in Group A. -/
#print axioms LeBrunSalamon.P1Charts.Binary
#print axioms LeBrunSalamon.P1Charts.ChartRing
#print axioms LeBrunSalamon.P1Charts.OverlapRing
#print axioms LeBrunSalamon.P1Charts.affineCover
#print axioms LeBrunSalamon.P1Charts.affinePoint_overC_is_eval
#print axioms LeBrunSalamon.P1Charts.canonicalBaseMap
#print axioms LeBrunSalamon.P1Charts.canonicalPoint_chart_dichotomy
#print axioms LeBrunSalamon.P1Charts.canonicalPoint_is_coordinate
#print axioms LeBrunSalamon.P1Charts.chartInclusion
#print axioms LeBrunSalamon.P1Charts.chartInclusion_baseMap
#print axioms LeBrunSalamon.P1Charts.chartInclusion_isOpenImmersion
#print axioms LeBrunSalamon.P1Charts.chartInclusion_preimage_chart
#print axioms LeBrunSalamon.P1Charts.chartInclusion_range
#print axioms LeBrunSalamon.P1Charts.chartIso
#print axioms LeBrunSalamon.P1Charts.chartOneToOverlap
#print axioms LeBrunSalamon.P1Charts.chartOpen
#print axioms LeBrunSalamon.P1Charts.chartOpen_affine
#print axioms LeBrunSalamon.P1Charts.chartOpen_cover
#print axioms LeBrunSalamon.P1Charts.chartOpen_zero_sup_one
#print axioms LeBrunSalamon.P1Charts.chartRingEquiv
#print axioms LeBrunSalamon.P1Charts.chartRingEquiv_symm_C
#print axioms LeBrunSalamon.P1Charts.chartRingEquiv_symm_X
#print axioms LeBrunSalamon.P1Charts.chartSectionsIso
#print axioms LeBrunSalamon.P1Charts.chartToPolynomial
#print axioms LeBrunSalamon.P1Charts.chartToPolynomial_fromZero
#print axioms LeBrunSalamon.P1Charts.chartToPolynomial_injective
#print axioms LeBrunSalamon.P1Charts.chartToPolynomial_mk
#print axioms LeBrunSalamon.P1Charts.chartToPolynomial_ratio
#print axioms LeBrunSalamon.P1Charts.chartToPolynomial_surjective
#print axioms LeBrunSalamon.P1Charts.chartZeroToOverlap
#print axioms LeBrunSalamon.P1Charts.constantsToZero
#print axioms LeBrunSalamon.P1Charts.coordinatePoints_distinct
#print axioms LeBrunSalamon.P1Charts.coordinateSubmonoid_map
#print axioms LeBrunSalamon.P1Charts.dehom
#print axioms LeBrunSalamon.P1Charts.dehom_X_other
#print axioms LeBrunSalamon.P1Charts.dehom_X_self
#print axioms LeBrunSalamon.P1Charts.dehom_one
#print axioms LeBrunSalamon.P1Charts.dehom_one_swap
#print axioms LeBrunSalamon.P1Charts.dehom_zero_swap
#print axioms LeBrunSalamon.P1Charts.grading
#print axioms LeBrunSalamon.P1Charts.homogeneous_dehom_eq_zero
#print axioms LeBrunSalamon.P1Charts.irrelevant_le_variableSpan
#print axioms LeBrunSalamon.P1Charts.lineScheme
#print axioms LeBrunSalamon.P1Charts.localizedDehom
#print axioms LeBrunSalamon.P1Charts.markedPoint
#print axioms LeBrunSalamon.P1Charts.overlapRingEquiv
#print axioms LeBrunSalamon.P1Charts.overlapRingEquiv_chartOne
#print axioms LeBrunSalamon.P1Charts.overlapRingEquiv_chartOne_constant
#print axioms LeBrunSalamon.P1Charts.overlapRingEquiv_chartZero
#print axioms LeBrunSalamon.P1Charts.overlapRingEquiv_ratioOne
#print axioms LeBrunSalamon.P1Charts.overlapRingEquiv_ratioZero
#print axioms LeBrunSalamon.P1Charts.overlapSchemeIso
#print axioms LeBrunSalamon.P1Charts.overlap_coordinates_inverse
#print axioms LeBrunSalamon.P1Charts.pointEval
#print axioms LeBrunSalamon.P1Charts.pointEval_constants
#print axioms LeBrunSalamon.P1Charts.pointEval_ratio
#print axioms LeBrunSalamon.P1Charts.pointMap
#print axioms LeBrunSalamon.P1Charts.pointMap_eq_polynomialChart
#print axioms LeBrunSalamon.P1Charts.pointMap_overC
#print axioms LeBrunSalamon.P1Charts.pointMap_preimage_chart
#print axioms LeBrunSalamon.P1Charts.point_chart_dichotomy
#print axioms LeBrunSalamon.P1Charts.point_factors_chart_of_mem
#print axioms LeBrunSalamon.P1Charts.point_factors_polynomialChart
#print axioms LeBrunSalamon.P1Charts.polynomialChartInclusion
#print axioms LeBrunSalamon.P1Charts.polynomialChartInclusion_baseMap
#print axioms LeBrunSalamon.P1Charts.polynomialChartInclusion_isOpenImmersion
#print axioms LeBrunSalamon.P1Charts.polynomialChartInclusion_range
#print axioms LeBrunSalamon.P1Charts.polynomialChartIso
#print axioms LeBrunSalamon.P1Charts.polynomialChartIso_hom_inclusion
#print axioms LeBrunSalamon.P1Charts.ratio
#print axioms LeBrunSalamon.P1Charts.swapBinary
#print axioms LeBrunSalamon.P1Charts.swapBinary_homogeneous
#print axioms LeBrunSalamon.P1Charts.swapBinary_involutive
#print axioms LeBrunSalamon.P1Charts.variable_degree
#print axioms LeBrunSalamon.P1Ideal.affineKernelIso
#print axioms LeBrunSalamon.P1Ideal.affineKernelLinearIso
#print axioms LeBrunSalamon.P1Ideal.affinePointIdealTrivialization
#print axioms LeBrunSalamon.P1Ideal.affinePointIdeal_rankOne
#print axioms LeBrunSalamon.P1Ideal.affineStructureKernelIso
#print axioms LeBrunSalamon.P1Ideal.affineStructureKernelLinearIso
#print axioms LeBrunSalamon.P1Ideal.canonicalPointIdeal_rankOne
#print axioms LeBrunSalamon.P1Ideal.locallyFreeOfRank_of_openCover
#print axioms LeBrunSalamon.P1Ideal.locallyFreeRankOne_of_restrictTrivial
#print axioms LeBrunSalamon.P1Ideal.polynomialEvalKernelEquiv
#print axioms LeBrunSalamon.P1Ideal.restrictTrivial_of_iso
#print axioms LeBrunSalamon.P1Ideal.restrict_preservesFiniteLimits
#print axioms LeBrunSalamon.P1Ideal.restrict_pushforward_unit_isZero
#print axioms LeBrunSalamon.P1Ideal.structureKernel_restrict_comp
#print axioms LeBrunSalamon.P1Ideal.structureKernel_restrict_disjoint
#print axioms LeBrunSalamon.P1Ideal.tilde_map_injective
#print axioms LeBrunSalamon.P1Ideal.tilde_map_mono
#print axioms LeBrunSalamon.P1Ideal.tilde_preservesHomology
#print axioms LeBrunSalamon.P1Ideal.tilde_preservesMonomorphisms
#print axioms LeBrunSalamon.P1Overlap.Matching
#print axioms LeBrunSalamon.P1Overlap.cechCokernelEquiv
#print axioms LeBrunSalamon.P1Overlap.cechCokernel_finite
#print axioms LeBrunSalamon.P1Overlap.cechCokernel_finrank
#print axioms LeBrunSalamon.P1Overlap.cechDifference
#print axioms LeBrunSalamon.P1Overlap.cechDifference_kernel
#print axioms LeBrunSalamon.P1Overlap.cechDifference_surjective
#print axioms LeBrunSalamon.P1Overlap.cechDifference_surjective_iff
#print axioms LeBrunSalamon.P1Overlap.cechEulerCharacteristic
#print axioms LeBrunSalamon.P1Overlap.coeff_mul_T
#print axioms LeBrunSalamon.P1Overlap.coeff_toLaurent_nat
#print axioms LeBrunSalamon.P1Overlap.coeff_toLaurent_neg
#print axioms LeBrunSalamon.P1Overlap.finitePointEvaluation
#print axioms LeBrunSalamon.P1Overlap.finitePointEvaluation_surjective
#print axioms LeBrunSalamon.P1Overlap.finitePointEvaluation_surjective_iff
#print axioms LeBrunSalamon.P1Overlap.gapProjection
#print axioms LeBrunSalamon.P1Overlap.gapProjection_kernel
#print axioms LeBrunSalamon.P1Overlap.gapProjection_surjective
#print axioms LeBrunSalamon.P1Overlap.isUnit_iff_monomial
#print axioms LeBrunSalamon.P1Overlap.markedEvaluation
#print axioms LeBrunSalamon.P1Overlap.markedEvaluation_not_surjective_nonpositive
#print axioms LeBrunSalamon.P1Overlap.markedEvaluation_surjective
#print axioms LeBrunSalamon.P1Overlap.markedEvaluation_surjective_iff
#print axioms LeBrunSalamon.P1Overlap.matchingSpace
#print axioms LeBrunSalamon.P1Overlap.matchingSpaceEquiv
#print axioms LeBrunSalamon.P1Overlap.matchingSpace_ext
#print axioms LeBrunSalamon.P1Overlap.matchingSpace_finite
#print axioms LeBrunSalamon.P1Overlap.matchingSpace_finrank
#print axioms LeBrunSalamon.P1Overlap.matchingSpace_finrank_all
#print axioms LeBrunSalamon.P1Overlap.matchingSpace_finrank_negative
#print axioms LeBrunSalamon.P1Overlap.matchingSpace_subsingleton_of_negative
#print axioms LeBrunSalamon.P1Overlap.matching_coeff
#print axioms LeBrunSalamon.P1Overlap.matching_degree_le
#print axioms LeBrunSalamon.P1Overlap.matching_evaluation_at_infinity
#print axioms LeBrunSalamon.P1Overlap.matching_first_injective
#print axioms LeBrunSalamon.P1Overlap.matching_iff_reflect
#print axioms LeBrunSalamon.P1Overlap.matching_negative
#print axioms LeBrunSalamon.P1Overlap.matching_reflect
#print axioms LeBrunSalamon.P1Overlap.monomial_mem_cechRange
#print axioms LeBrunSalamon.P1Overlap.monomial_unique
#print axioms LeBrunSalamon.P1Overlap.unit_is_monomial
#print axioms LeBrunSalamon.P1Restriction.restrictPushforwardIso
#print axioms LeBrunSalamon.P1Restriction.restrict_structurePushforwardMap
#print axioms LeBrunSalamon.P1Restriction.restrict_structurePushforwardMap_comp
#print axioms LeBrunSalamon.P1Restriction.structureKernel_precomposeIso
#print axioms LeBrunSalamon.P1Restriction.structurePushforwardMap_isIso
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveLine_hasDistinctPoints
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveLine_hasPoint
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveMinusOneLine
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.bilinearToHom
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.commHom
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.commHom_pair
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.commIso
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.flip
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.homToBilinear
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.leftUnitHom
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.leftUnitHom_pair
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.leftUnitInv
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.leftUnitIso
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.presentation
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.presheaf
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.presheafHomEquiv
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.scalarPair
#print axioms LeBrunSalamon.PhaseTwentyFive.TensorConstruction.sheafHomEquiv
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorPresentation
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorSheaf_comm
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorSheaf_leftUnit
#print axioms LeBrunSalamon.PhaseTwentyFive.tensorSheaf_rightUnit
#print axioms LeBrunSalamon.PhaseTwentySix.freeSheaf_rank
#print axioms LeBrunSalamon.PhaseTwentySix.locallyFreeOfRank_iso
#print axioms LeBrunSalamon.PhaseTwentySix.structureModule_rank
#print axioms LeBrunSalamon.PhaseTwentySix.trivialLine
#print axioms LeBrunSalamon.PhaseTwo.ProjectiveLinePoint.ext
#print axioms LeBrunSalamon.PhaseTwo.ProjectiveLinePoint.rebase
#print axioms LeBrunSalamon.PhaseTwo.ProjectiveLinePoint.rebaseEquiv
#print axioms LeBrunSalamon.PhaseTwo.ProjectiveLinePoint.rebase_map_eq_iff
#print axioms LeBrunSalamon.PhaseTwo.ProjectiveLinePoint.rebase_rebase
#print axioms LeBrunSalamon.PhaseTwo.ProjectiveLinePoint.rebase_self
#print axioms LeBrunSalamon.Project.projectiveLineAtlasAndPointIdealConstructed
#print axioms LeBrunSalamon.Project.projectiveLineBundleTheoryComplete
#print axioms LeBrunSalamon.PhaseTwentySix.dualLine
#print axioms LeBrunSalamon.PhaseTwentySix.tensorLine
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveOneLine



/- Source-only relocation: the original PhaseNine theorem follows from the actual
P1 splitting/evaluation criteria, whose definitions and proofs precede this insertion. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseEighteen

namespace LeBrunSalamon.PhaseNine

/-- A very free curve is free. The distinct pair is supplied by the original
interpolation predicate. The approved Birkhoff--Grothendieck theorem gives a
splitting of the actual pullback bundle, and the established two-point and
global-generation criteria respectively give degrees at least one and at least zero. -/
theorem veryFree_implies_free
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (TX : AlgebraicVectorBundle X.scheme d)
    (f : RationalCurve P X)
    (hf : IsVeryFreeRationalCurve P X TX f) :
    IsFreeRationalCurve P X TX f := by
  let E : AlgebraicVectorBundle ProjectiveLine d :=
    ⟨pullbackModule f.map TX.sheaf,
      LeBrunSalamon.PhaseTwentySix.pullback_locallyFree f.map TX.locallyFree⟩
  obtain ⟨p, q, hpq⟩ := hf.1
  obtain ⟨a, ha⟩ := LeBrunSalamon.PhaseThirtyTwo.birkhoffGrothendieck P p E
  have hpos : a.IsVeryFree :=
    (LeBrunSalamon.PhaseThirtyTwo.splitBundle_twoPointEvaluation_iff P p q hpq E a ha).mp
      (hf.2 p q hpq)
  change IsGloballyGenerated E.sheaf
  apply (LeBrunSalamon.PhaseThirtyTwo.splitBundle_globallyGenerated_iff P p E a ha).mpr
  intro i
  have hi := hpos i
  omega

end LeBrunSalamon.PhaseNine
end

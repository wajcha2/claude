import LSFamilyDescentReparametrization
import LSOpenSectionTransport
import LSFamilySmoothCoordinates
import LSFamilySmoothPointValues
import LSFamilySmoothDescent

/-!
# Open-section comparison and smooth-family descent of the actual tensors.

This namespace block is extracted verbatim from the candidate descent
source. Public names, statements and proof bodies are retained. The preceding
transport blocks are imported so each completed native output can be reused.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.Construction.FamilyBivectors


-- Normalize the existing P1/contact carrier aliases for the same actual maps.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

private theorem covered_pull_map {T Y W Z : Scheme}
    (a : T ⟶ Y) (b : Y ⟶ Z) (c : T ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) {V L : OModule Z} (v : V ⟶ L)
    (s : AlgebraicSection (pullbackModule b V))
    (t : AlgebraicSection (pullbackModule d V))
    (hs : pullSection a s ≫ (pullbackSquareIso a b c d h V).hom = pullSection c t) :
    pullSection a (s ≫ (Scheme.Modules.pullback b).map v) ≫
        (pullbackSquareIso a b c d h L).hom =
      pullSection c (t ≫ (Scheme.Modules.pullback d).map v) := by
  rw [pullSection_naturality a s ((Scheme.Modules.pullback b).map v),
    Category.assoc, pullbackSquare_naturality a b c d h v,
    ← Category.assoc, hs,
    ← pullSection_naturality c t ((Scheme.Modules.pullback d).map v)]

private theorem extension_covered_identity
    {P : ProjectiveLineOverC} {n : ℕ} {X : ContactFanoManifold n}
    {Y T : Scheme} (r : Y ⟶ SelfProduct X.variety.structureMap)
    (R : MovingPair.RationalVectorPair (X := X) r) (E : R.Extension)
    (hp : IsProper r) (hd : DenseRange (fun y : Y => r y)) (hI : Descent.IntegralScheme Y)
    (f : RationalCurve P X.variety) (a : T ⟶ Y) (c : T ⟶ SelfProduct P.structureMap)
    (h : a ≫ r = c ≫ curveSquareMap P f)
    (hs : pullSection a E.leftSection ≫
        (pullbackSquareIso a r c (curveSquareMap P f) h
          (movingPairBundleLeft X.variety X.contact)).hom =
      pullSection c (Curve.leftSection P X f)) :
    pullSection a (E.properPair hp hd hI).value ≫
        (pullbackSquareIso a (E.properPair hp hd hI).pair.data.projection c
          (curveSquareMap P f) h
          (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf).hom =
      pullSection c (sourceContactValue P X.contact f) := by
  change pullSection a (E.properPair hp hd hI).value ≫
      (pullbackSquareIso a r c (curveSquareMap P f) h
        (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf).hom = _
  calc
    _ = pullSection a
        (E.leftSection ≫ (Scheme.Modules.pullback r).map
          (movingPairContactLeft X.variety X.contact)) ≫
        (pullbackSquareIso a r c (curveSquareMap P f) h
          (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf).hom := by
      exact congrArg
        (fun w : AlgebraicSection (pullbackModule r
          (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf) =>
            pullSection a w ≫
              (pullbackSquareIso a r c (curveSquareMap P f) h
                (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf).hom)
        (E.properPair_value hp hd hI)
    _ = pullSection c
        (Curve.leftSection P X f ≫ (Scheme.Modules.pullback (curveSquareMap P f)).map
          (movingPairContactLeft X.variety X.contact)) :=
      covered_pull_map a r c (curveSquareMap P f) h
        (movingPairContactLeft X.variety X.contact) E.leftSection (Curve.leftSection P X f) hs
    _ = pullSection c (sourceContactValue P X.contact f) :=
      congrArg
        (fun w : AlgebraicSection (pullbackModule (curveSquareMap P f)
          (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf) => pullSection c w)
        (Curve.leftSection_contact P X f)

private def extension_covered_comparison
    {P : ProjectiveLineOverC} {n : ℕ} {X : ContactFanoManifold n}
    {Y T : Scheme} (r : Y ⟶ SelfProduct X.variety.structureMap)
    (R : MovingPair.RationalVectorPair (X := X) r) (E : R.Extension)
    (hp : IsProper r) (hd : DenseRange (fun y : Y => r y)) (hI : Descent.IntegralScheme Y)
    (f : RationalCurve P X.variety) (a : T ⟶ Y) (c : T ⟶ SelfProduct P.structureMap)
    (h : a ≫ r = c ≫ curveSquareMap P f)
    (hc : IsProper c) (hcs : Function.Surjective (fun z : T => c z))
    (hs : pullSection a E.leftSection ≫
        (pullbackSquareIso a r c (curveSquareMap P f) h
          (movingPairBundleLeft X.variety X.contact)).hom =
      pullSection c (Curve.leftSection P X f)) :
    CoveredCurveComparison P X (E.properPair hp hd hI) f where
  cover := T
  toSquare := c
  proper := hc
  surjective := hcs
  toSource := a
  commutes := h
  identity := extension_covered_identity r R E hp hd hI f a c h hs

namespace SmoothFamily

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)


variable (t : PointsOver ComplexBase (𝟙 ComplexBase) N.neighborhood.toScheme
  (N.neighborhood.ι ≫ N.homSpace.toC))

/-- An actual extension yields the exact original covered-curve
comparison. The contact value is the original normalized source tensor. -/
def coveredComparison (E : (rationalPair Q).Extension)
    (hp : IsProper F.squareEvaluation)
    (hd : DenseRange (fun y : F.Square => F.squareEvaluation y)) :
    CoveredCurveComparison P X (E.properPair hp hd F.square_integralScheme) (N.curveAt t) :=
  extension_covered_comparison (P := P) (X := X) (Y := F.Square)
    (T := Q.ReducedMemberCover t) F.squareEvaluation (rationalPair Q) E
    hp hd F.square_integralScheme (N.curveAt t)
    (memberToFamily Q t) (Q.reducedMemberToSquare t)
    (memberToFamily_evaluation Q t) (Q.reducedMemberToSquare_proper t)
    (Q.reducedMemberToSquare_surjective t) (extension_left_member Q t E)

/-- The original covered moving-pair output follows from extension of
the two rational sections. All full-family comparisons are constructed,
rather than added as a field of an auxiliary hypothesis package. -/
def coveredMovingPair (E : (rationalPair Q).Extension)
    (hd : DenseRange (fun y : F.Square => F.squareEvaluation y)) :
    CoveredMovingPair P p X g where
  properPair := E.properPair F.squareEvaluation_proper hd F.square_integralScheme
  fullFamily := N
  comparison := fun t => coveredComparison Q t E F.squareEvaluation_proper hd

end SmoothFamily

end LeBrunSalamon.Construction.FamilyBivectors

end

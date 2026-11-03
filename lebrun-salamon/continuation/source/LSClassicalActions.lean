import LSHamiltonianJets
import LSRelativeGenericSmoothness
import LSContactLineTests

/-!
# From actual open contact orbits to an actual transitive action

The algebraic group, its regular action, and its infinitesimal orbit
criterion are separate classical inputs. This file proves the remaining
transitivity step on the actual scheme. The common orbit point is lifted
through the actual scheme pullback to an actual complex-valued point.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.ClassicalActions

/-- The original regular-action laws, with transitivity still to prove. -/
structure EffectiveContactAction {n : ℕ} (X : ContactFanoManifold n) where
  group : ConnectedAlgebraicGroup
  data : RegularActionData group X.variety
  unitLaw : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (x : PointsOver T sT X.variety.scheme X.variety.structureMap),
    data.applyPoint (group.data.oneAt T sT) x = x
  actionLaw : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (g h : PointsOver T sT group.data.scheme group.data.toC)
    (x : PointsOver T sT X.variety.scheme X.variety.structureMap),
    data.applyPoint (group.data.mulAt g h) x = data.applyPoint g (data.applyPoint h x)
  contact : ∀ g : PointsOver ComplexBase (𝟙 ComplexBase) group.data.scheme group.data.toC,
    ∃ e : ContactIso X.variety X.variety X.contact X.contact,
      e.schemeIso.hom = data.translation g
  effective : ∀ g : PointsOver ComplexBase (𝟙 ComplexBase) group.data.scheme group.data.toC,
    (∀ x : PointsOver ComplexBase (𝟙 ComplexBase) X.variety.scheme X.variety.structureMap,
      data.applyPoint g x = x) → g = group.data.oneAt ComplexBase (𝟙 ComplexBase)

namespace EffectiveContactAction

variable {n : ℕ} {X : ContactFanoManifold n} (A : EffectiveContactAction X)

/-- The actual orbit morphism of the specified complex point. -/
def orbit (x : PointsOver ComplexBase (𝟙 ComplexBase)
    X.variety.scheme X.variety.structureMap) : A.group.data.scheme ⟶ X.variety.scheme :=
  pullback.lift (𝟙 A.group.data.scheme) (A.group.data.toC ≫ x.val)
    (by simp only [Category.id_comp, Category.assoc, x.property, Category.comp_id]) ≫
      A.data.action

theorem orbit_overC (x : PointsOver ComplexBase (𝟙 ComplexBase)
    X.variety.scheme X.variety.structureMap) :
    A.orbit x ≫ X.variety.structureMap = A.group.data.toC := by
  simp only [orbit, Category.assoc, A.data.overC, pullback.lift_snd_assoc,
    x.property, Category.comp_id]

theorem orbit_point
    (x : PointsOver ComplexBase (𝟙 ComplexBase) X.variety.scheme X.variety.structureMap)
    (g : PointsOver ComplexBase (𝟙 ComplexBase) A.group.data.scheme A.group.data.toC) :
    g.val ≫ A.orbit x = (A.data.applyPoint g x).val := by
  dsimp only [orbit, RegularActionData.applyPoint, pairOver]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [Category.assoc, g.property]

theorem orbit_range_nonempty
    (x : PointsOver ComplexBase (𝟙 ComplexBase) X.variety.scheme X.variety.structureMap) :
    (Set.range (A.orbit x)).Nonempty := by
  let e := A.group.data.unit (IsLocalRing.closedPoint ℂ)
  exact ⟨A.orbit x e, e, rfl⟩

/-- Nonempty open orbits meet on an irreducible variety. The actual
pullback of the two orbit maps supplies a common complex orbit point,
so multiplying one group element by the inverse of the other gives the
required transporter. No abstract point permutation action is used. -/
theorem transitive_of_open_orbits [IrreducibleSpace X.variety.scheme]
    (hopen : ∀ x : PointsOver ComplexBase (𝟙 ComplexBase)
      X.variety.scheme X.variety.structureMap, IsOpen (Set.range (A.orbit x))) :
    ∀ x y : PointsOver ComplexBase (𝟙 ComplexBase)
      X.variety.scheme X.variety.structureMap,
      ∃ g, A.data.applyPoint g x = y := by
  intro x y
  letI : Smooth A.group.data.toC := A.group.smooth
  haveI : LocallyOfFiniteType (A.orbit y ≫ X.variety.structureMap) := by
    rw [A.orbit_overC]
    infer_instance
  haveI : LocallyOfFiniteType (A.orbit y) :=
    locallyOfFiniteType_of_comp (A.orbit y) X.variety.structureMap
  obtain ⟨z, ⟨a, ha⟩, ⟨b, hb⟩⟩ := nonempty_preirreducible_inter
    (hopen x) (hopen y) (A.orbit_range_nonempty x) (A.orbit_range_nonempty y)
  obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := A.orbit x) (g := A.orbit y) a b (ha.trans hb.symm)
  let sW : pullback (A.orbit x) (A.orbit y) ⟶ ComplexBase :=
    pullback.fst (A.orbit x) (A.orbit y) ≫ A.group.data.toC
  have hbase : pullback.snd (A.orbit x) (A.orbit y) ≫ A.group.data.toC = sW := by
    calc
      _ = pullback.snd (A.orbit x) (A.orbit y) ≫
          (A.orbit y ≫ X.variety.structureMap) := by rw [A.orbit_overC]
      _ = (pullback.snd (A.orbit x) (A.orbit y) ≫ A.orbit y) ≫
          X.variety.structureMap := (Category.assoc _ _ _).symm
      _ = (pullback.fst (A.orbit x) (A.orbit y) ≫ A.orbit x) ≫
          X.variety.structureMap := by rw [pullback.condition]
      _ = sW := by simp only [sW, Category.assoc, A.orbit_overC]
  obtain ⟨q, hq, _⟩ :=
    LeBrunSalamon.Construction.Lines.RelativeGenericSmoothness.exists_point_in_nonempty_open
      sW ⊤ ⟨w, trivial⟩
  let g : PointsOver ComplexBase (𝟙 ComplexBase) A.group.data.scheme A.group.data.toC :=
    ⟨q ≫ pullback.fst (A.orbit x) (A.orbit y), by
      simpa only [Category.assoc, sW] using hq⟩
  let h : PointsOver ComplexBase (𝟙 ComplexBase) A.group.data.scheme A.group.data.toC :=
    ⟨q ≫ pullback.snd (A.orbit x) (A.orbit y), by
      rw [Category.assoc, hbase]
      exact hq⟩
  have he : A.data.applyPoint g x = A.data.applyPoint h y := by
    apply Subtype.ext
    rw [← A.orbit_point, ← A.orbit_point]
    dsimp only [g, h]
    simp only [Category.assoc, pullback.condition]
  refine ⟨A.group.data.mulAt (A.group.data.invAt h) g, ?_⟩
  calc
    A.data.applyPoint (A.group.data.mulAt (A.group.data.invAt h) g) x =
        A.data.applyPoint (A.group.data.invAt h) (A.data.applyPoint g x) :=
      A.actionLaw _ _ _ _ _
    _ = A.data.applyPoint (A.group.data.invAt h) (A.data.applyPoint h y) := by rw [he]
    _ = A.data.applyPoint (A.group.data.mulAt (A.group.data.invAt h) h) y :=
      (A.actionLaw _ _ _ _ _).symm
    _ = A.data.applyPoint (A.group.data.oneAt ComplexBase (𝟙 ComplexBase)) y := by
      rw [A.group.inv_mul]
    _ = y := A.unitLaw _ _ _

/-- The original target action, including the transitivity just proved. -/
def toAlgebraicContactAction [IrreducibleSpace X.variety.scheme]
    (hopen : ∀ x : PointsOver ComplexBase (𝟙 ComplexBase)
      X.variety.scheme X.variety.structureMap, IsOpen (Set.range (A.orbit x))) :
    AlgebraicContactAction X where
  group := A.group
  data := A.data
  unitLaw := A.unitLaw
  actionLaw := A.actionLaw
  contact := A.contact
  effective := A.effective
  transitive := A.transitive_of_open_orbits hopen

end EffectiveContactAction

namespace StandardInputs

/- Classical neutral contact automorphism group and local orbit criterion.
Beauville 1998, Section 1 before Proposition 1.1: Aut^0(X,F) is an
algebraic group with Lie algebra the actual global contact fields.
Proposition 1.1 identifies those fields with H0(X,L), with contact-value
map as inverse. The supplied intrinsicHamiltonianSectionField is that
unique contact lift, so no arbitrary linear identification is used.

For a Fano manifold, a sufficiently high anticanonical power is very
ample and is canonically linearized. The faithful projective action
realizes Aut(X) as a closed subgroup of PGL; its contact stabilizer and
neutral component are affine, smooth in characteristic zero, connected,
and effective. The action and laws are actual scheme morphisms with
their identities on ALL test schemes, including nonreduced schemes.

At any complex point, the orbit differential is evaluation of global
contact fields. Surjectivity makes the orbit open, by the classical
smooth-orbit criterion in characteristic zero. This statement only
gives that local criterion; transitivity is separately proved in
LSClassicalActions from actual intersections/pullbacks and complex
points. It asserts neither HamiltoniansSpan X nor first-jet generation.
-/
theorem contactAutomorphismGroup_localOrbits {n : ℕ}
    (X : ContactFanoManifold n) :
    ∃ A : EffectiveContactAction X,
      ∀ x : ComplexPoint X.variety,
        (∀ v : TangentEvaluationAt n (intrinsicAsCandidate X.variety X.contact) x,
          ∃ a : AlgebraicSection X.contact.sequence.line.sheaf,
            restrictSection x.map
              (intrinsicHamiltonianSectionField X.variety X.contact a) = v) →
        IsOpen (Set.range (A.orbit ⟨x.map, x.overC⟩)) := by
  sorry


end StandardInputs


/-- Actual infinitesimal spanning yields the original transitive algebraic
contact action. Transitivity uses the ordinary orbit-intersection proof,
not a transitivity field supplied by the classical input. -/
theorem algebraicIntegration : AlgebraicIntegration := by
  intro n X h
  letI : GeometricallyIntegral X.variety.structureMap :=
    LeBrunSalamon.StandardInputs.smooth_connected_complex_geometricallyIntegral
      X.variety.structureMap
  letI : IsIntegral X.variety.scheme :=
    GeometricallyIntegral.isIntegral_of_subsingleton X.variety.structureMap
  obtain ⟨A, hA⟩ := StandardInputs.contactAutomorphismGroup_localOrbits X
  refine ⟨A.toAlgebraicContactAction ?_⟩
  intro x
  exact hA ⟨x.val, x.property⟩ (h ⟨x.val, x.property⟩)

end LeBrunSalamon.ClassicalActions

end

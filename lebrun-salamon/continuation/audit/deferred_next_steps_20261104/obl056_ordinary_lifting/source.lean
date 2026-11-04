import LSRelativeHomLiftingCorrespondenceProbe

/-! Actual evaluation form of the lifting correspondence for the supplied
relative Hom presentation. No infinitesimal or cohomological input is used. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.RelativeMorphismsFunctorPrototype

namespace LeBrunSalamon.Next3i.PresentationLifting

/-- Projection of the base-changed target map is the original map to X. -/
theorem targetChange_fst {S Y : Scheme} (pi : Y ⟶ S)
    (sS : S ⟶ ComplexBase) {d : ℕ} (X : SmoothProperComplexVariety d)
    (T : Over S)
    (g : {g : pullback pi T.hom ⟶ X.scheme //
      g ≫ X.structureMap = pullback.snd pi T.hom ≫ T.hom ≫ sS}) :
    (targetChangeEquiv pi sS X T g).left ≫ pullback.fst X.structureMap sS = g.val := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- The checked representability equivalence retains the actual universal
evaluation after projection to X. -/
theorem representation_fst {S Y : Scheme} (pi : Y ⟶ S)
    (sS : S ⟶ ComplexBase) {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomDeformationInput.Presentation pi sS X)
    {T : Over S} (a : T ⟶ Over.mk H.toBase) :
    ((presentationRepresentation pi sS X H).homEquiv a).left ≫
        pullback.fst X.structureMap sS =
      HomDeformationInput.familyChange pi T.hom H.toBase a.left a.w ≫ H.evaluation := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- A lift in the given parameter scheme is equivalent to a lift of the
literal evaluated source family, with both structural equations retained.
The test morphism i is arbitrary; square-zero tests are a specialization. -/
theorem lift_iff_evaluation {S Y : Scheme} (pi : Y ⟶ S)
    (sS : S ⟶ ComplexBase) {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomDeformationInput.Presentation pi sS X)
    {T₀ T : Scheme} (t₀ : T₀ ⟶ S) (t : T ⟶ S)
    (i : T₀ ⟶ T) (hi : i ≫ t = t₀)
    (a₀ : T₀ ⟶ H.parameter) (ha₀ : a₀ ≫ H.toBase = t₀) :
    (∃ a : T ⟶ H.parameter, a ≫ H.toBase = t ∧ i ≫ a = a₀) ↔
      ∃ g : pullback pi t ⟶ X.scheme,
        g ≫ X.structureMap = pullback.snd pi t ≫ t ≫ sS ∧
        HomDeformationInput.familyChange pi t₀ t i hi ≫ g =
          HomDeformationInput.familyChange pi t₀ H.toBase a₀ ha₀ ≫ H.evaluation := by
  let iO : (Over.mk t₀ : Over S) ⟶ Over.mk t := Over.homMk i hi
  let a₀O : (Over.mk t₀ : Over S) ⟶ Over.mk H.toBase := Over.homMk a₀ ha₀
  let R := presentationRepresentation pi sS X H
  have hiff := RelativeHomLifting.lift_iff_family pi
    (pullback.snd X.structureMap sS) (Over.mk H.toBase) R iO a₀O
  constructor
  · rintro ⟨a, ha, hia⟩
    let aO : (Over.mk t : Over S) ⟶ Over.mk H.toBase := Over.homMk a ha
    have hiaO : iO ≫ aO = a₀O := by
      apply Over.OverMorphism.ext
      exact hia
    obtain ⟨G, hG⟩ := hiff.mp ⟨aO, hiaO⟩
    let g := (targetChangeEquiv pi sS X (Over.mk t)).symm G
    refine ⟨g.val, g.property, ?_⟩
    have hfst := congrArg
      (fun u : sourceOver pi (Over.mk t₀) ⟶
          Over.mk (pullback.snd X.structureMap sS) =>
        u.left ≫ pullback.fst X.structureMap sS) hG
    change (HomDeformationInput.familyChange pi t₀ t i hi ≫ G.left) ≫
        pullback.fst X.structureMap sS =
      (R.homEquiv a₀O).left ≫ pullback.fst X.structureMap sS at hfst
    change HomDeformationInput.familyChange pi t₀ t i hi ≫
        (G.left ≫ pullback.fst X.structureMap sS) = _
    exact (Category.assoc _ _ _).symm.trans
      (hfst.trans (representation_fst pi sS X H a₀O))
  · rintro ⟨g, hg, hrestrict⟩
    let G := targetChangeEquiv pi sS X (Over.mk t) ⟨g, hg⟩
    have hGfst : G.left ≫ pullback.fst X.structureMap sS = g :=
      targetChange_fst pi sS X (Over.mk t) ⟨g, hg⟩
    have hG : sourceMapOver pi iO ≫ G = R.homEquiv a₀O := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change (HomDeformationInput.familyChange pi t₀ t i hi ≫ G.left) ≫
            pullback.fst X.structureMap sS =
          (R.homEquiv a₀O).left ≫ pullback.fst X.structureMap sS
        rw [Category.assoc, hGfst]
        exact hrestrict.trans (representation_fst pi sS X H a₀O).symm
      · exact (sourceMapOver pi iO ≫ G).w.trans (R.homEquiv a₀O).w.symm
    obtain ⟨a, ha⟩ := hiff.mpr ⟨G, hG⟩
    refine ⟨a.left, a.w, ?_⟩
    exact congrArg (fun f : (Over.mk t₀ : Over S) ⟶ Over.mk H.toBase => f.left) ha

/-- The original complex point and prescribed fibre map specialize the
same correspondence without a new smoothness or cohomology assumption. -/
theorem point_lift_iff_evaluation {S Y : Scheme} (pi : Y ⟶ S)
    (sS : S ⟶ ComplexBase) {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomDeformationInput.Presentation pi sS X)
    (p : ComplexBase ⟶ H.parameter) (b : ComplexBase ⟶ S)
    (hb : p ≫ H.toBase = b)
    {T : Scheme} (t : T ⟶ S) (i : ComplexBase ⟶ T) (hi : i ≫ t = b) :
    (∃ a : T ⟶ H.parameter, a ≫ H.toBase = t ∧ i ≫ a = p) ↔
      ∃ g : pullback pi t ⟶ X.scheme,
        g ≫ X.structureMap = pullback.snd pi t ≫ t ≫ sS ∧
        HomDeformationInput.familyChange pi b t i hi ≫ g =
          HomDeformationInput.familyChange pi b H.toBase p hb ≫ H.evaluation :=
  lift_iff_evaluation pi sS X H b t i hi p hb

end LeBrunSalamon.Next3i.PresentationLifting

end

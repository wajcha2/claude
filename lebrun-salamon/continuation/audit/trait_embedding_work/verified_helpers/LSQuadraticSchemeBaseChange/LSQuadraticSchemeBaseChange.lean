import LSPlaneQuadraticBaseChange

/-! Coefficientwise base change of the actual quadratic zero scheme.
The cartesian squares are proved from the section-zero universal property
and the normalized projective and tensor-square comparisons. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement

namespace LeBrunSalamon.QuadraticSchemeBaseChange

theorem section_zero_iff {X Y T : Scheme.{0}} (b : X ⟶ Y)
    {E : OModule Y} {F : OModule X} (e : pullbackModule b E ≅ F)
    (s : AlgebraicSection E) (t : AlgebraicSection F)
    (he : pullSection b s ≫ e.hom = t) (f : T ⟶ X) :
    pullSection (f ≫ b) s = 0 ↔ pullSection f t = 0 := by
  let c := ((Scheme.Modules.pullbackComp f b).app E).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e
  have hc : pullSection (f ≫ b) s ≫ c.hom = pullSection f t := by
    have h := StandardProjectiveBaseChange.composite_coordinate f b s e
      (Iso.refl (pullbackModule f F))
    simpa only [Iso.trans_refl, Iso.refl_hom, Category.comp_id, he] using h
  constructor
  · intro h
    rw [← hc, h, zero_comp]
  · intro h
    apply (cancel_mono c.hom).mp
    rw [hc, h, zero_comp]

theorem pullSection_comp_zero {X Y T : Scheme.{0}} (i : X ⟶ Y)
    {E : OModule Y} (s : AlgebraicSection E) (hi : pullSection i s = 0) (f : T ⟶ X) :
    pullSection (f ≫ i) s = 0 := by
  have h := CanonicalPullbackSectionProof.pullSection_comp f i s
  rw [hi] at h
  simpa only [pullSection, restrictSection, Functor.map_zero, comp_zero, zero_comp] using h.symm

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
  (q : PlaneQuadratic.Coefficients R)

abbrev coefficients : PlaneQuadratic.Coefficients S := fun k => φ (q k)

theorem zero_iff {T : Scheme.{0}} (f : T ⟶ PlaneQuadratic.Plane S) :
    pullSection (f ≫ StandardProjectiveBaseChange.map φ 2) (PlaneQuadratic.sectionOf R q) = 0 ↔
      pullSection f (PlaneQuadratic.sectionOf S (coefficients φ q)) = 0 :=
  section_zero_iff (StandardProjectiveBaseChange.map φ 2)
    (PlaneQuadraticBaseChange.squareLineIso φ 2)
    (PlaneQuadratic.sectionOf R q) (PlaneQuadratic.sectionOf S (coefficients φ q))
    (PlaneQuadraticBaseChange.sectionOf φ q) f

def map : PlaneQuadratic.ZeroScheme S (coefficients φ q) ⟶ PlaneQuadratic.ZeroScheme R q :=
  Classical.choose (PlaneQuadratic.universal R q
    (PlaneQuadratic.inclusion S (coefficients φ q) ≫ StandardProjectiveBaseChange.map φ 2)
    ((zero_iff φ q (PlaneQuadratic.inclusion S (coefficients φ q))).mpr
      (PlaneQuadratic.zero_equation S (coefficients φ q))))

@[reassoc] theorem map_inclusion : map φ q ≫ PlaneQuadratic.inclusion R q =
    PlaneQuadratic.inclusion S (coefficients φ q) ≫ StandardProjectiveBaseChange.map φ 2 :=
  (Classical.choose_spec (PlaneQuadratic.universal R q
    (PlaneQuadratic.inclusion S (coefficients φ q) ≫ StandardProjectiveBaseChange.map φ 2)
    ((zero_iff φ q (PlaneQuadratic.inclusion S (coefficients φ q))).mpr
      (PlaneQuadratic.zero_equation S (coefficients φ q))))).1

theorem universal {T : Scheme.{0}}
    (f : T ⟶ PlaneQuadratic.ZeroScheme R q) (g : T ⟶ PlaneQuadratic.Plane S)
    (h : f ≫ PlaneQuadratic.inclusion R q = g ≫ StandardProjectiveBaseChange.map φ 2) :
    ∃! w : T ⟶ PlaneQuadratic.ZeroScheme S (coefficients φ q),
      w ≫ map φ q = f ∧ w ≫ PlaneQuadratic.inclusion S (coefficients φ q) = g := by
  have hz := pullSection_comp_zero (PlaneQuadratic.inclusion R q)
    (PlaneQuadratic.sectionOf R q) (PlaneQuadratic.zero_equation R q) f
  rw [h] at hz
  obtain ⟨w, hw, _⟩ := PlaneQuadratic.universal S (coefficients φ q) g
    ((zero_iff φ q g).mp hz)
  refine ⟨w, ⟨?_, hw⟩, ?_⟩
  · apply (cancel_mono (PlaneQuadratic.inclusion R q)).mp
    rw [Category.assoc, map_inclusion, ← Category.assoc, hw, h]
  · intro z hz
    exact (cancel_mono (PlaneQuadratic.inclusion S (coefficients φ q))).mp (hz.2.trans hw.symm)

theorem isPullback_inclusion : IsPullback (map φ q)
    (PlaneQuadratic.inclusion S (coefficients φ q)) (PlaneQuadratic.inclusion R q)
    (StandardProjectiveBaseChange.map φ 2) := by
  refine ⟨⟨map_inclusion φ q⟩, ⟨?_⟩⟩
  apply PullbackCone.IsLimit.mk _
    (fun c => Classical.choose (universal φ q c.fst c.snd c.condition))
  · intro c
    exact (Classical.choose_spec (universal φ q c.fst c.snd c.condition)).1.1
  · intro c
    exact (Classical.choose_spec (universal φ q c.fst c.snd c.condition)).1.2
  · intro c m hm₁ hm₂
    exact (Classical.choose_spec (universal φ q c.fst c.snd c.condition)).2 m ⟨hm₁, hm₂⟩

theorem isPullback : IsPullback (map φ q)
    (PlaneQuadratic.projection S (coefficients φ q)) (PlaneQuadratic.projection R q)
    (StandardProjectiveBaseChange.base φ) :=
  (isPullback_inclusion φ q).paste_vert (StandardProjectiveBaseChange.isPullback φ 2)

def fibreIso : PlaneQuadratic.ZeroScheme S (coefficients φ q) ≅
    pullback (PlaneQuadratic.projection R q) (StandardProjectiveBaseChange.base φ) :=
  (isPullback φ q).isoPullback

@[reassoc] theorem fibreIso_projection : (fibreIso φ q).hom ≫
    pullback.snd (PlaneQuadratic.projection R q) (StandardProjectiveBaseChange.base φ) =
      PlaneQuadratic.projection S (coefficients φ q) :=
  (isPullback φ q).isoPullback_hom_snd

end LeBrunSalamon.QuadraticSchemeBaseChange
end

import RecompileSections

/-!
Picard classification in the actual marked-point convention. The only new
published input is triviality of the Picard group of Spec of a UFD (Stacks
0BDA). Both chart frames, their Laurent transition, its constant rescaling,
and the isomorphism to the already constructed projectiveTwist are explicit.
This candidate remains outside the live source until native verification.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.LocalFrames
open scoped LaurentPolynomial

namespace LeBrunSalamon.PublishedInputs.Picard

/-- Stacks Project, Lemma 31.29.4, Tag 0BDA, part (1).
Triviality of Pic(Spec R) says precisely that every invertible sheaf is
isomorphic to the unit sheaf. The base ring is an arbitrary UFD; the leaf
does not mention projective space, a marked point, or a chosen twist.
-/
theorem affineUFD_trivial (R : Type) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (L : (Spec (CommRingCat.of R)).Modules) (hL : IsLocallyFreeOfRank L 1) :
    Nonempty (structureModule (Spec (CommRingCat.of R)) ≅ L) := by
  sorry

end LeBrunSalamon.PublishedInputs.Picard

namespace LeBrunSalamon.P1PicardTranslation

/-- The supplied line sheaf is trivial on each actual polynomial chart.
Restriction is compared with pullback before the generic UFD theorem is used.
-/
def chartFrame (L : LineBundle ProjectiveLine) (i : Fin 2) :
    OverFrame L.sheaf (chartOpen i) := by
  let j := polynomialChartInclusion i
  let F := pullbackModule j L.sheaf
  let e : structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅ F :=
    Classical.choice (PublishedInputs.Picard.affineUFD_trivial (Polynomial ℂ) F
      (pullback_locallyFree j L.locallyFree))
  let ep : structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      L.sheaf.restrict j :=
    e ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback j).app L.sheaf).symm
  let eo : structureModule (chartOpen i).toScheme ≅
      L.sheaf.restrict (chartOpen i).ι :=
    (P1Ideal.restrictTrivial_of_iso L.sheaf (chartOpen i).ι j
      (polynomialChartIso i) (polynomialChartIso_hom_inclusion i) ep.symm).symm
  exact ofOpenFrame (chartOpen i) eo

/-- Restriction preserves the comparison of two specified frames. -/
theorem restrict_comparison {X : Scheme} {E F : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (f : OverFrame F U) :
    P1Ideal.restrictOverIso i (e.symm ≪≫ f) =
      (restrict i e).symm ≪≫ restrict i f := by
  apply Iso.ext
  simp [P1Ideal.restrictOverIso, restrict, Functor.map_comp, Category.assoc]

/-- Equality of the actual transition functions gives equality of the actual
frame-comparison maps on every smaller open, by their naturality. -/
theorem comparison_eq_of_transition {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e e' : OverFrame E U) (f f' : OverFrame F U)
    (h : transition e e' = transition f f') : e.symm ≪≫ f = e'.symm ≪≫ f' := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  let j : W.unop ⟶ Over.mk (𝟙 U) := Over.homMk W.unop.hom
  have ht := congrArg
    (fun a => (X.sheaf.over U).obj.map j.op a) h
  change (X.sheaf.over U).obj.map j.op
      (Generic.transition (R := X.sheaf.over U) e e' (Over.mk (𝟙 U))) =
    (X.sheaf.over U).obj.map j.op
      (Generic.transition (R := X.sheaf.over U) f f' (Over.mk (𝟙 U))) at ht
  rw [Generic.transition_naturality, Generic.transition_naturality] at ht
  apply (Generic.coordinates (R := X.sheaf.over U) f W.unop).injective
  change Generic.coordinates (R := X.sheaf.over U) f W.unop
      ((Generic.coordinates (R := X.sheaf.over U) f W.unop).symm
        (Generic.coordinates (R := X.sheaf.over U) e W.unop x)) =
    Generic.coordinates (R := X.sheaf.over U) f W.unop
      ((Generic.coordinates (R := X.sheaf.over U) f' W.unop).symm
        (Generic.coordinates (R := X.sheaf.over U) e' W.unop x))
  rw [LinearEquiv.apply_symm_apply,
    Generic.coordinates_change (R := X.sheaf.over U) e e',
    Generic.coordinates_change (R := X.sheaf.over U) f f',
    LinearEquiv.apply_symm_apply, ht]

/-- Two actual over-site isomorphisms glue from one overlap equation. -/
def glueOverPairIso {X : Scheme} {E F : X.Modules} (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (eU : E.over U ≅ F.over U) (eV : E.over V ≅ F.over V)
    (h : P1Ideal.restrictOverIso (homOfLE (inf_le_left : U ⊓ V ≤ U)) eU =
      P1Ideal.restrictOverIso (homOfLE (inf_le_right : U ⊓ V ≤ V)) eV) : E ≅ F := by
  let O : Fin 2 → X.Opens := Fin.cases U (fun _ => V)
  have hc : iSup O = ⊤ := by
    apply le_antisymm le_top
    rw [← hcover]
    exact sup_le (le_iSup O 0) (le_iSup O 1)
  let e : ∀ i, E.over (O i) ≅ F.over (O i) := Fin.cases eU (fun _ => eV)
  apply P1Ideal.glueOverIso O hc e
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact h
  · change P1Ideal.restrictOverIso (homOfLE (inf_le_left : V ⊓ U ≤ V)) eV =
      P1Ideal.restrictOverIso (homOfLE (inf_le_right : V ⊓ U ≤ U)) eU
    have hs : ∀ (Z : X.Opens) (hZV : Z ≤ V) (hZU : Z ≤ U), Z = U ⊓ V →
        P1Ideal.restrictOverIso (homOfLE hZV) eV =
          P1Ideal.restrictOverIso (homOfLE hZU) eU := by
      intro Z hZV hZU hZ
      subst Z
      exact h.symm
    exact hs (V ⊓ U) inf_le_left inf_le_right (inf_comm V U)
  · rfl

def isoOfTransition {X : Scheme} {E F : X.Modules} (U V : X.Opens)
    (hcover : U ⊔ V = ⊤)
    (e₀ : OverFrame E U) (e₁ : OverFrame E V)
    (f₀ : OverFrame F U) (f₁ : OverFrame F V)
    (h : transition (restrict (homOfLE inf_le_left) e₀)
        (restrict (homOfLE inf_le_right) e₁) =
      transition (restrict (homOfLE inf_le_left) f₀)
        (restrict (homOfLE inf_le_right) f₁)) : E ≅ F :=
  glueOverPairIso U V hcover (e₀.symm ≪≫ f₀) (e₁.symm ≪≫ f₁) (by
    rw [restrict_comparison, restrict_comparison]
    exact comparison_eq_of_transition _ _ _ _ h)

/-- Rescale a specified frame by a genuine global constant automorphism. -/
def scaleFrame {E : ProjectiveLine.Modules} {U : ProjectiveLine.Opens}
    (e : OverFrame E U) (c : ℂˣ) : OverFrame E U :=
  e ≪≫ (SheafOfModules.overFunctor ProjectiveLine.ringCatSheaf U).mapIso
    (P1Endomorphisms.complexScalarIso E c)

theorem restricted_scale_transition {E : ProjectiveLine.Modules}
    (e₀ : OverFrame E (chartOpen 0)) (e₁ : OverFrame E (chartOpen 1)) (c : ℂˣ) :
    transition (restrict (homOfLE inf_le_left) (scaleFrame e₀ c))
        (restrict (homOfLE inf_le_right) e₁) =
      ProjectiveLine.presheaf.map (homOfLE le_top).op
        (P1Endomorphisms.canonicalConstantRingHom (c.inv)) *
      transition (restrict (homOfLE inf_le_left) e₀)
        (restrict (homOfLE inf_le_right) e₁) := by
  change e₀.inv.val.app (op (Over.mk (homOfLE inf_le_left)))
      ((GlobalScalars.scalarEnd E
        (P1Endomorphisms.canonicalConstantRingHom c.inv)).app
          (chartOpen 0 ⊓ chartOpen 1)
          (generator (restrict (homOfLE inf_le_right) e₁))) = _
  rw [GlobalScalars.scalarEnd_app]
  exact (e₀.inv.val.app (op (Over.mk (homOfLE inf_le_left)))).hom.map_smul _ _

theorem overlap_constant (c : ℂ) :
    overlapRingCoordinates (ProjectiveLine.presheaf.map (homOfLE le_top).op
      (P1Endomorphisms.canonicalConstantRingHom c)) = LaurentPolynomial.C c := by
  have h := polynomialChartRingEquiv_canonical_constant 0 c
  let r := P1Endomorphisms.canonicalConstantRingHom c
  change polynomialChartRingEquiv 0
    (ProjectiveLine.presheaf.map (homOfLE le_top).op r) = Polynomial.C c at h
  change overlapRingCoordinates (ProjectiveLine.presheaf.map (homOfLE le_top).op r) = _
  calc
    _ = overlapRingCoordinates (ProjectiveLine.presheaf.map (homOfLE inf_le_left).op
        (ProjectiveLine.presheaf.map
          (homOfLE (show chartOpen 0 ≤ ⊤ from le_top)).op r)) := by
      congr 1
    _ = zeroRestrictionRingHom (polynomialChartRingEquiv 0
        (ProjectiveLine.presheaf.map (homOfLE le_top).op r)) := by
      change _ = overlapRingCoordinates (ProjectiveLine.presheaf.map
        (homOfLE inf_le_left).op ((polynomialChartRingEquiv 0).symm
          (polynomialChartRingEquiv 0
            (ProjectiveLine.presheaf.map (homOfLE le_top).op r))))
      rw [RingEquiv.symm_apply_apply]
    _ = zeroRestrictionRingHom (Polynomial.C c) := congrArg zeroRestrictionRingHom h
    _ = LaurentPolynomial.C c := by
      rw [zeroRestrictionRingHom_eq_toLaurent, Polynomial.toLaurent_C]

/-- The old Picard admission, now proved by two affine frames, the Laurent-unit
calculation, a specified scalar normalization, and actual sheaf gluing. -/
theorem lineBundleClassification (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (L : LineBundle ProjectiveLine) :
    ∃! d : ℤ, Nonempty (L.sheaf ≅ (projectiveTwist P p d).sheaf) := by
  let e₀ := chartFrame L 0
  let e₁ := chartFrame L 1
  let t := transitionUnit (restrict (homOfLE inf_le_left) e₀)
    (restrict (homOfLE inf_le_right) e₁)
  have ht : IsUnit (overlapRingCoordinates (t : RingSections ProjectiveLine
      (chartOpen 0 ⊓ chartOpen 1))) := t.isUnit.map overlapRingCoordinates.toRingHom
  obtain ⟨c, d, hc, hcd⟩ := P1Overlap.unit_is_monomial _ ht
  let u : ℂˣ := Units.mk0 c hc
  have htransition :
      transition (restrict (homOfLE inf_le_left) (scaleFrame e₀ u))
          (restrict (homOfLE inf_le_right) e₁) =
        transition (restrict (homOfLE inf_le_left) (twistOverFrame P p d 0))
          (restrict (homOfLE inf_le_right) (twistOverFrame P p d 1)) := by
    apply overlapRingCoordinates.injective
    rw [restricted_scale_transition, map_mul, overlap_constant]
    change LaurentPolynomial.C (u.inv) * overlapRingCoordinates (t.val) = _
    rw [hcd]
    change LaurentPolynomial.C c⁻¹ *
      (LaurentPolynomial.C c * LaurentPolynomial.T d) = (laurentTransitionUnit P p d).val
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul,
      laurentTransitionUnit_eq_T]
  let e := isoOfTransition (chartOpen 0) (chartOpen 1) chartOpen_zero_sup_one
    (scaleFrame e₀ u) e₁ (twistOverFrame P p d 0) (twistOverFrame P p d 1) htransition
  refine ⟨d, ⟨e⟩, ?_⟩
  intro k hk
  obtain ⟨ek⟩ := hk
  exact P1TwistSections.exponent_eq_of_iso P p k d (ek.symm ≪≫ e)

end LeBrunSalamon.P1PicardTranslation

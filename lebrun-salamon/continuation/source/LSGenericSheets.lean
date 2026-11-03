import RecompileExtensionsPart04
import LSLineValueDescent

/-!
The actual generic finite image of the contact value.  A source point is
allowed to have any residue field over the function field of the test line.
Its reduced closure is proper and integral, so the component-section theorem
places its image on a scalar graph.  The closed-image argument then descends
that image point to the ground field.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction.Lines
open LeBrunSalamon.P1Charts

namespace LeBrunSalamon.StandardInputs

/-- Published finite-presentation spreading, specialized to a finite
morphism over an integral locally noetherian base.  Stacks Project,
Lemma 32.10.1, Tag 01ZM, parts (2) and (3), spreads the given isomorphism,
its inverse, their identities, and their commutativity with the base.
The generic splitting itself is an explicit hypothesis, not a conclusion. -/
theorem finite_generic_trivialization_spreads {X Y : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] (q : Y ⟶ X) [IsFinite q]
    (m : ℕ)
    (e : pullback q (X.fromSpecStalk (genericPoint X)) ≅
      ∐ (fun _ : Fin m => Spec X.functionField))
    (he : e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 (Spec X.functionField)) =
      pullback.snd q (X.fromSpecStalk (genericPoint X))) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧
      ∃ eU : pullback q U.ι ≅ ∐ (fun _ : Fin m => U.toScheme),
        eU.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 U.toScheme) =
          pullback.snd q U.ι := by sorry

end LeBrunSalamon.StandardInputs

namespace LeBrunSalamon.Construction.Descent.GenericSheets

/-- Base change of a specified morphism over the actual base. -/
def baseChangeMap {A B Z W : Scheme} (f : A ⟶ Z) (g : B ⟶ Z)
    (a : A ⟶ B) (ha : a ≫ g = f) (c : W ⟶ Z) :
    pullback f c ⟶ pullback g c :=
  pullback.lift (pullback.fst f c ≫ a) (pullback.snd f c)
    (by rw [Category.assoc, ha, pullback.condition])

@[reassoc (attr := simp)]
theorem baseChangeMap_fst {A B Z W : Scheme} (f : A ⟶ Z) (g : B ⟶ Z)
    (a : A ⟶ B) (ha : a ≫ g = f) (c : W ⟶ Z) :
    baseChangeMap f g a ha c ≫ pullback.fst g c = pullback.fst f c ≫ a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeMap_snd {A B Z W : Scheme} (f : A ⟶ Z) (g : B ⟶ Z)
    (a : A ⟶ B) (ha : a ≫ g = f) (c : W ⟶ Z) :
    baseChangeMap f g a ha c ≫ pullback.snd g c = pullback.snd f c :=
  pullback.lift_snd _ _ _

theorem baseChangeMap_isPullback {A B Z W : Scheme} (f : A ⟶ Z) (g : B ⟶ Z)
    (a : A ⟶ B) (ha : a ≫ g = f) (c : W ⟶ Z) :
    IsPullback (pullback.fst f c) (baseChangeMap f g a ha c)
      a (pullback.fst g c) := by
  apply IsPullback.of_bot (t := IsPullback.of_hasPullback g c)
  · simpa only [baseChangeMap_snd, ha] using IsPullback.of_hasPullback f c
  · simp only [baseChangeMap_fst]

instance baseChangeMap_closed {A B Z W : Scheme} (f : A ⟶ Z) (g : B ⟶ Z)
    (a : A ⟶ B) (ha : a ≫ g = f) (c : W ⟶ Z) [IsClosedImmersion a] :
    IsClosedImmersion (baseChangeMap f g a ha c) :=
  MorphismProperty.of_isPullback (baseChangeMap_isPullback f g a ha c) inferInstance

instance baseChangeMap_surjective {A B Z W : Scheme} (f : A ⟶ Z) (g : B ⟶ Z)
    (a : A ⟶ B) (ha : a ≫ g = f) (c : W ⟶ Z) [Surjective a] :
    Surjective (baseChangeMap f g a ha c) :=
  MorphismProperty.of_isPullback (baseChangeMap_isPullback f g a ha c) inferInstance

/-- A point over a field extension on a closed scalar graph gives a point
over the original field.  No rational point of the source is required. -/
theorem closed_factor_through_field {K F : Type} [Field K] [Field F]
    {Y E : Scheme} (i : Y ⟶ E) [IsClosedImmersion i]
    (g : Spec (CommRingCat.of K) ⟶ E)
    (a : Spec (CommRingCat.of F) ⟶ Y)
    (b : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
    (h : a ≫ i = b ≫ g) :
    ∃ r : Spec (CommRingCat.of K) ⟶ Y, r ≫ i = g ∧ b ≫ r = a := by
  let l : Spec (CommRingCat.of F) ⟶ pullback i g := pullback.lift a b h
  letI : Nonempty (pullback i g : Scheme) := ⟨l (IsLocalRing.closedPoint F)⟩
  letI : IsIso (pullback.snd i g) :=
    isIso_of_isClosedImmersion_of_surjective (pullback.snd i g)
  let r : Spec (CommRingCat.of K) ⟶ Y :=
    inv (pullback.snd i g) ≫ pullback.fst i g
  have hr : r ≫ i = g := by
    simp only [r, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  refine ⟨r, hr, ?_⟩
  apply (cancel_mono i).mp
  rw [Category.assoc, hr, ← h]

/-- The scheme-theoretic image of a field-valued point is the reduced
irreducible closure of that point. -/
theorem field_image_integral {F : Type} [Field F] {Y : Scheme}
    (a : Spec (CommRingCat.of F) ⟶ Y) : IsIntegral a.image := by
  letI : QuasiCompact a := ⟨fun U _ _ => (Set.toFinite (a ⁻¹' U)).isCompact⟩
  letI : AlgebraicGeometry.IsReduced a.image := FiniteImageProof.image_reduced a
  letI : IrreducibleSpace a.image := by
    apply (irreducibleSpace_def a.image).mpr
    change IsIrreducible (Set.univ : Set a.image)
    have h := (IrreducibleSpace.isIrreducible_univ (Spec (CommRingCat.of F))).image
      a.toImage a.toImage.continuous.continuousOn
    simpa only [Set.image_univ, a.toImage.denseRange.closure_eq] using h.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced a.image

/-- The actual pullback-square comparison agrees with the two actual
composition comparisons. -/
theorem square_comp_comparison {T Y W Z : Scheme}
    (a : T ⟶ Y) (b : Y ⟶ Z) (c : T ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) (E : OModule Z) :
    (pullbackSquareIso a b c d h E).hom ≫
        (compositionPullback c d (c ≫ d) rfl E).hom =
      (compositionPullback a b (c ≫ d) h E).hom := by
  simp only [pullbackSquareIso, compositionPullback, Iso.trans_hom,
    Iso.symm_hom, eqToIso.hom, eqToHom_refl, Category.comp_id,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- Equality of the actual sections in a square is equality of their
representing morphisms to the total line. -/
theorem section_square_map {T Y W Z : Scheme} {L : LineBundle Z}
    (E : TotalLine L) (a : T ⟶ Y) (b : Y ⟶ Z) (c : T ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d)
    (v : AlgebraicSection (pullbackModule b L.sheaf))
    (w : AlgebraicSection (pullbackModule d L.sheaf))
    (hw : pullSection c w = pullSection a v ≫
      (pullbackSquareIso a b c d h L.sheaf).hom) :
    a ≫ (E.mapOfSection b v).val = c ≫ (E.mapOfSection d w).val := by
  rw [E.mapOfSection_naturality b a (c ≫ d) h v,
    E.mapOfSection_naturality d c (c ≫ d) rfl w]
  apply congrArg (fun s => (E.mapOfSection (c ≫ d) s).val)
  rw [hw, Category.assoc, square_comp_comparison]

/-- The component-section result is used on the actual closed source,
with its value still tied to the original finite-image inclusion. -/
theorem component_map_factors {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) (I : FiniteValueImage D)
    (f : FreeLine X) (y : ComplexPoint X.variety) (axis : Axis)
    {T : Scheme} [IsIntegral T] (pi : T ⟶ ProjectiveLine)
    [IsProper (pi ≫ P.structureMap)] (d : T ⟶ D.pair.data.source)
    (hd : d ≫ D.pair.data.projection = pi ≫ testLine f y axis) :
    ∃ a : AlgebraicSection (pullbackModule (testLine f y axis) (SquareLine X).sheaf),
      d ≫ I.fromSource ≫ I.inclusion =
        pi ≫ (I.total.mapOfSection (testLine f y axis) a).val := by
  obtain ⟨a, ha⟩ := LineValue.component_section D f y axis pi d hd
  refine ⟨a, ?_⟩
  rw [I.imageEquation]
  exact section_square_map I.total d D.pair.data.projection pi
    (testLine f y axis) hd D.value a ha

section SchemePullbackPoints

-- Fix the intended category when a scheme pullback is coerced to its point type.
local notation "pullback" => (CategoryTheory.Limits.pullback (C := Scheme))

/-- Every point of the actual finite image over a field mapping to the
test line is rational over that field.  Its lift to the proper source is
first closed up over the whole line; the lift itself may be non-rational. -/
theorem image_points_rational {K : Type} [Field K]
    {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) (I : FiniteValueImage D)
    (f : FreeLine X) (y : ComplexPoint X.variety) (axis : Axis)
    (eta : Spec (CommRingCat.of K) ⟶ ProjectiveLine)
    (x : pullback I.projection (eta ≫ testLine f y axis)) :
    ∃ r : Spec (CommRingCat.of K) ⟶
        pullback I.projection (eta ≫ testLine f y axis),
      r ≫ pullback.snd I.projection (eta ≫ testLine f y axis) = 𝟙 _ ∧
      r (IsLocalRing.closedPoint K) = x := by
  let c := testLine f y axis
  let p := D.pair.data.projection
  let S := pullback p (eta ≫ c)
  let Y := pullback p c
  letI : Surjective I.fromSource := ⟨I.sourceSurjective⟩
  let aS : S ⟶ pullback I.projection (eta ≫ c) :=
    baseChangeMap p I.projection I.fromSource I.sourceOver (eta ≫ c)
  obtain ⟨t, ht⟩ := aS.surjective x
  let k : S ⟶ Y := pullback.lift (pullback.fst p (eta ≫ c))
    (pullback.snd p (eta ≫ c) ≫ eta)
    (by rw [Category.assoc, pullback.condition])
  let a : Spec (S.residueField t) ⟶ Y := S.fromSpecResidueField t ≫ k
  letI : IsIntegral a.image := field_image_integral a
  let pi : a.image ⟶ ProjectiveLine := a.imageι ≫ pullback.snd p c
  let d : a.image ⟶ D.pair.data.source := a.imageι ≫ pullback.fst p c
  letI : IsProper p := D.pair.data.proper
  letI : IsProper P.structureMap := ProjectiveLineProof.structureMap_proper P
  letI : IsProper (pi ≫ P.structureMap) := by dsimp [pi]; infer_instance
  have hd : d ≫ p = pi ≫ c := by
    simp only [d, pi, Category.assoc, pullback.condition]
  obtain ⟨v, hv⟩ := component_map_factors D I f y axis pi d hd
  let b : Spec (S.residueField t) ⟶ Spec (CommRingCat.of K) :=
    S.fromSpecResidueField t ≫ pullback.snd p (eta ≫ c)
  let j := baseChangeMap I.projection I.total.projection I.inclusion
    I.overSquare (eta ≫ c)
  let g : Spec (CommRingCat.of K) ⟶ pullback I.total.projection (eta ≫ c) :=
    pullback.lift (eta ≫ (I.total.mapOfSection c v).val) (𝟙 _)
      (by rw [Category.assoc, (I.total.mapOfSection c v).property, Category.id_comp])
  let u : Spec (S.residueField t) ⟶ pullback I.projection (eta ≫ c) :=
    S.fromSpecResidueField t ≫ aS
  letI : IsClosedImmersion I.inclusion := I.closed
  have hu : u ≫ j = b ≫ g := by
    apply pullback.hom_ext
    · have hv' := congrArg (fun h => a.toImage ≫ h) hv
      simpa only [a, k, pi, d, aS, u, j, b, g, Category.assoc,
        Scheme.Hom.toImage_imageι_assoc, baseChangeMap_fst,
        baseChangeMap_fst_assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc] using hv'
    · simp only [u, j, aS, b, g, Category.assoc, baseChangeMap_snd,
        pullback.lift_snd, Category.comp_id]
  obtain ⟨r, hr, hbr⟩ := closed_factor_through_field j g u b hu
  refine ⟨r, ?_, ?_⟩
  · have h := congrArg (fun h => h ≫ pullback.snd I.total.projection (eta ≫ c)) hr
    simpa only [j, g, Category.assoc, baseChangeMap_snd, pullback.lift_snd] using h
  · have h := congrArg (fun h : Spec (S.residueField t) ⟶
        pullback I.projection (eta ≫ c) => h (IsLocalRing.closedPoint (S.residueField t))) hbr
    simpa only [Scheme.Hom.comp_apply, u, Scheme.fromSpecResidueField_apply,
      show b (IsLocalRing.closedPoint (S.residueField t)) = IsLocalRing.closedPoint K from
        Subsingleton.elim _ _, ht] using h

end SchemePullbackPoints

/-- Rational points over the actual structure morphism give rational
prime quotients of the actual affine coordinate algebra. -/
theorem rational_prime_residues {K B : Type} [Field K] [CommRing B] [Algebra K B]
    (h : ∀ x : Spec (CommRingCat.of B),
      ∃ r : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B),
        r ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) = 𝟙 _ ∧
        r (IsLocalRing.closedPoint K) = x) :
    SheetAlgebra.RationalPrimeResidues K B := by
  intro p hp
  obtain ⟨r, hr, hx⟩ := h ⟨p, hp⟩
  obtain ⟨phi, rfl⟩ := Spec.map_surjective r
  have hphi : CommRingCat.ofHom (algebraMap K B) ≫ phi = 𝟙 _ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_id] using hr
  let a : B →ₐ[K] K := {
    toRingHom := phi.hom
    commutes' := fun c => congrArg (fun k : CommRingCat.of K ⟶ CommRingCat.of K => k c) hphi }
  have hker : RingHom.ker a.toRingHom = p := by
    have hx' := congrArg PrimeSpectrum.asIdeal hx
    change Ideal.comap phi.hom (IsLocalRing.closedPoint K).asIdeal = p at hx'
    rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint K).asIdeal] at hx'
    exact hx'
  have ha : Function.Surjective a := fun c => ⟨algebraMap K B c, a.commutes c⟩
  exact ⟨(Ideal.quotientEquivAlgOfEq K hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective ha)⟩

/-- The coefficient map supplied by an actual scheme morphism to a
field spectrum. -/
def scalarMap {K : Type} [Field K] {Y : Scheme}
    (q : Y ⟶ Spec (CommRingCat.of K)) : CommRingCat.of K ⟶ Γ(Y, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop

theorem scalarMap_structure {K : Type} [Field K] {Y : Scheme} [IsAffine Y]
    (q : Y ⟶ Spec (CommRingCat.of K)) :
    Y.isoSpec.hom ≫ Spec.map (scalarMap q) = q := by
  simp only [scalarMap, Scheme.isoSpec, asIso_hom, Spec.map_comp,
    ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom]
  simp

theorem scalarMap_structure_inv {K : Type} [Field K] {Y : Scheme} [IsAffine Y]
    (q : Y ⟶ Spec (CommRingCat.of K)) :
    Y.isoSpec.inv ≫ q = Spec.map (scalarMap q) := by
  rw [Iso.inv_comp_eq]
  exact (scalarMap_structure q).symm

/-- Finite étaleness supplies precisely the two algebraic facts needed
by SheetAlgebra: finite dimension and reducedness. -/
theorem finite_etale_rational_split {K : Type} [Field K] {Y : Scheme}
    (q : Y ⟶ Spec (CommRingCat.of K)) [IsFinite q] [Etale q] [Nonempty Y]
    (h : ∀ x : Y, ∃ r : Spec (CommRingCat.of K) ⟶ Y,
      r ≫ q = 𝟙 _ ∧ r (IsLocalRing.closedPoint K) = x) :
    ∃ m : ℕ, 0 < m ∧ ∃ e : Y ≅ ∐ (fun _ : Fin m => Spec (CommRingCat.of K)),
      e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 (Spec (CommRingCat.of K))) = q := by
  classical
  letI : IsAffine Y := isAffine_of_isAffineHom q
  letI : Nonempty (⊤ : Y.Opens) := ⟨⟨Classical.choice (inferInstance : Nonempty Y), trivial⟩⟩
  letI : Algebra K Γ(Y, ⊤) := (scalarMap q).hom.toAlgebra
  have hfinite : (scalarMap q).hom.Finite := by
    apply RingHom.finite_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
    exact q.finite_appTop
  letI : FiniteDimensional K Γ(Y, ⊤) := hfinite
  have hetale : (scalarMap q).hom.Etale := by
    apply RingHom.Etale.respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  letI : Algebra.Etale K Γ(Y, ⊤) := hetale
  letI : _root_.IsReduced Γ(Y, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field K Γ(Y, ⊤)
  have hres : SheetAlgebra.RationalPrimeResidues K Γ(Y, ⊤) := by
    apply rational_prime_residues
    intro x
    obtain ⟨r, hr, hx⟩ := h (Y.isoSpec.inv x)
    refine ⟨r ≫ Y.isoSpec.hom, ?_, ?_⟩
    · change (r ≫ Y.isoSpec.hom) ≫ Spec.map (scalarMap q) =
        𝟙 (Spec (CommRingCat.of K))
      rw [Category.assoc, scalarMap_structure]
      exact hr
    · simp only [Scheme.Hom.comp_apply, hx]
      exact congrArg (fun k : Spec Γ(Y, ⊤) ⟶ Spec Γ(Y, ⊤) => k x)
        Y.isoSpec.inv_hom_id
  obtain ⟨m, ⟨a⟩⟩ := SheetAlgebra.finite_reduced_rational_isSplit K Γ(Y, ⊤) hres
  let ea : Spec Γ(Y, ⊤) ≅ Spec (CommRingCat.of (Fin m → K)) :=
    Scheme.Spec.mapIso a.toRingEquiv.toCommRingCatIso.symm.op
  let e : Y ≅ ∐ (fun _ : Fin m => Spec (CommRingCat.of K)) :=
    Y.isoSpec ≪≫ ea ≪≫ (asIso (sigmaSpec (fun _ : Fin m => CommRingCat.of K))).symm
  have he : e.inv ≫ q =
      Sigma.desc (fun _ : Fin m => 𝟙 (Spec (CommRingCat.of K))) := by
    apply Sigma.hom_ext
    intro i
    simp only [e, Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc,
      ι_sigmaSpec_assoc, scalarMap_structure_inv, Sigma.ι_comp_desc]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => K) i)) ≫
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map (scalarMap q) = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_comp]
    have hmap : scalarMap q ≫ CommRingCat.ofHom a.toRingHom ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => K) i) = 𝟙 _ := by
      apply CommRingCat.hom_ext
      ext c
      exact congrArg (fun w : Fin m → K => w i) (a.commutes c)
    rw [Category.assoc, hmap, Spec.map_id]
  refine ⟨m, SheetAlgebra.split_nontrivial_positive K Γ(Y, ⊤) m a, e, ?_⟩
  rw [← he, Iso.hom_inv_id_assoc]

/-- The morphism from a base change to the restriction over an open. -/
def toOpenBase {Y Z W : Scheme} (q : Y ⟶ Z) (U : Z.Opens)
    (c : W ⟶ Z) (cU : W ⟶ U.toScheme) (hc : cU ≫ U.ι = c) :
    pullback q c ⟶ pullback q U.ι :=
  pullback.lift (pullback.fst q c) (pullback.snd q c ≫ cU)
    (by rw [Category.assoc, hc, pullback.condition])

@[reassoc (attr := simp)]
theorem toOpenBase_fst {Y Z W : Scheme} (q : Y ⟶ Z) (U : Z.Opens)
    (c : W ⟶ Z) (cU : W ⟶ U.toScheme) (hc : cU ≫ U.ι = c) :
    toOpenBase q U c cU hc ≫ pullback.fst q U.ι = pullback.fst q c :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem toOpenBase_snd {Y Z W : Scheme} (q : Y ⟶ Z) (U : Z.Opens)
    (c : W ⟶ Z) (cU : W ⟶ U.toScheme) (hc : cU ≫ U.ι = c) :
    toOpenBase q U c cU hc ≫ pullback.snd q U.ι = pullback.snd q c ≫ cU :=
  pullback.lift_snd _ _ _

theorem toOpenBase_isPullback {Y Z W : Scheme} (q : Y ⟶ Z) (U : Z.Opens)
    (c : W ⟶ Z) (cU : W ⟶ U.toScheme) (hc : cU ≫ U.ι = c) :
    IsPullback (toOpenBase q U c cU hc) (pullback.snd q c)
      (pullback.snd q U.ι) cU := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback q U.ι)
  · simpa only [toOpenBase_fst, hc] using IsPullback.of_hasPullback q c
  · simp only [toOpenBase_snd]

theorem etale_baseChange_of_open {Y Z W : Scheme} (q : Y ⟶ Z) (U : Z.Opens)
    (c : W ⟶ Z) (cU : W ⟶ U.toScheme) (hc : cU ≫ U.ι = c)
    (h : Etale (pullback.snd q U.ι)) : Etale (pullback.snd q c) :=
  MorphismProperty.of_isPullback (toOpenBase_isPullback q U c cU hc) h

/-- The actual comparison between base changes remains an isomorphism
when the new base maps into the specified isomorphism open. -/
theorem baseChangeMap_iso_of_open {A B Z W : Scheme} (f : A ⟶ Z) (g : B ⟶ Z)
    (a : A ⟶ B) (ha : a ≫ g = f) (U : Z.Opens)
    (hU : IsIso (baseChangeMap f g a ha U.ι))
    (c : W ⟶ Z) (cU : W ⟶ U.toScheme) (hc : cU ≫ U.ι = c) :
    IsIso (baseChangeMap f g a ha c) := by
  have hpb : IsPullback (toOpenBase f U c cU hc) (baseChangeMap f g a ha c)
      (baseChangeMap f g a ha U.ι) (toOpenBase g U c cU hc) := by
    apply IsPullback.of_bot (t := toOpenBase_isPullback g U c cU hc)
    · simpa only [baseChangeMap_snd] using toOpenBase_isPullback f U c cU hc
    · apply pullback.hom_ext <;> simp only [Category.assoc, baseChangeMap_fst,
        baseChangeMap_fst_assoc, baseChangeMap_snd, baseChangeMap_snd_assoc,
        toOpenBase_fst, toOpenBase_fst_assoc, toOpenBase_snd, toOpenBase_snd_assoc]
  exact hpb.isIso_snd_of_isIso hU

/-- Each actual polynomial chart is irreducible. -/
theorem projectiveLine_chart_irreducible (i : Fin 2) :
    IsIrreducible (LeBrunSalamon.P1Charts.chartOpen i : Set ProjectiveLine) := by
  have h := (IrreducibleSpace.isIrreducible_univ
    (Spec (CommRingCat.of (Polynomial ℂ)))).image
      (LeBrunSalamon.P1Charts.polynomialChartInclusion i)
      (LeBrunSalamon.P1Charts.polynomialChartInclusion i).continuous.continuousOn
  rw [Set.image_univ] at h
  change IsIrreducible
    ((LeBrunSalamon.P1Charts.polynomialChartInclusion i).opensRange : Set ProjectiveLine) at h
  rw [LeBrunSalamon.P1Charts.polynomialChartInclusion_range] at h
  exact h

/-- The two nonempty irreducible open polynomial charts meet, hence
their actual union P1 is irreducible. -/
theorem projectiveLine_irreducible : IrreducibleSpace ProjectiveLine := by
  have hmeet (U : Set ProjectiveLine) (hU : IsOpen U) (hUn : U.Nonempty) :
      ((chartOpen 0 : Set ProjectiveLine) ∩ U).Nonempty := by
    obtain ⟨x, hx⟩ := hUn
    by_cases hx0 : x ∈ chartOpen 0
    · exact ⟨x, hx0, hx⟩
    have hx1 : x ∈ chartOpen 1 := by
      have ht : x ∈ chartOpen 0 ⊔ chartOpen 1 := by
        rw [chartOpen_zero_sup_one]
        trivial
      exact (show x ∈ chartOpen 0 ∨ x ∈ chartOpen 1 from ht).resolve_left hx0
    obtain ⟨z, hz, hz'⟩ := (projectiveLine_chart_irreducible 1).2
      U (chartOpen 0) hU (chartOpen 0).isOpen ⟨x, hx1, hx⟩
      ⟨pointMap 0 1 (default : PrimeSpectrum ℂ),
        ProjectiveLineProof.coordinateOne_mem_chart 1,
        ProjectiveLineProof.coordinateOne_mem_chart 0⟩
    exact ⟨z, hz'.2, hz'.1⟩
  letI : PreirreducibleSpace ProjectiveLine :=
    PreirreducibleSpace.of_forall_nonempty_inter (fun {U V} hU hV hUn hVn => by
      obtain ⟨z, hzU, hzV⟩ := (projectiveLine_chart_irreducible 0).2
        U V hU hV (hmeet U hU hUn) (hmeet V hV hVn)
      exact ⟨z, hzV.1, hzV.2⟩)
  exact { toPreirreducibleSpace := inferInstance
          toNonempty := ProjectiveLineProof.projectiveLine_nonempty }

theorem projectiveLine_integral : IsIntegral ProjectiveLine := by
  letI : IrreducibleSpace ProjectiveLine := projectiveLine_irreducible
  letI : Smooth P.structureMap := smoothProperComplexVariety_smooth (projectiveLineVariety P)
  letI : AlgebraicGeometry.IsReduced ProjectiveLine :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced P.structureMap
  exact isIntegral_of_irreducibleSpace_of_isReduced ProjectiveLine

/-- Actual base change of the normalized image over a field mapping
into the good open.  The original finite image gives every rational point,
and the original normalization comparison transports them. -/
theorem normalized_field_split {K : Type} [Field K]
    {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) (I : FiniteValueImage D) (N : NormalizedImage I)
    (U : GoodOpen N) (f : FreeLine X) (y : ComplexPoint X.variety) (axis : Axis)
    (eta : Spec (CommRingCat.of K) ⟶ ProjectiveLine)
    (hU : Set.range (eta ≫ testLine f y axis) ⊆ (U.openSet : Set (Square X))) :
    ∃ m : ℕ, 0 < m ∧
      ∃ e : pullback N.cover.map (eta ≫ testLine f y axis) ≅
          ∐ (fun _ : Fin m => Spec (CommRingCat.of K)),
        e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 (Spec (CommRingCat.of K))) =
          pullback.snd N.cover.map (eta ≫ testLine f y axis) := by
  let c := eta ≫ testLine f y axis
  let cU : Spec (CommRingCat.of K) ⟶ U.openSet.toScheme :=
    IsOpenImmersion.lift U.openSet.ι c (by simpa only [Scheme.Opens.range_ι] using hU)
  have hc : cU ≫ U.openSet.ι = c := IsOpenImmersion.lift_fac _ _ _
  let a := baseChangeMap N.cover.map I.projection N.normalization N.overSquare c
  letI : IsIso a := baseChangeMap_iso_of_open N.cover.map I.projection
    N.normalization N.overSquare U.openSet U.unchanged c cU hc
  letI : Etale (pullback.snd N.cover.map c) :=
    etale_baseChange_of_open N.cover.map U.openSet c cU hc U.etale
  letI : IsDominant N.cover.map := ⟨N.cover.dominant⟩
  letI : Surjective N.cover.map :=
    surjective_of_isDominant_of_isClosed_range N.cover.map
      N.cover.map.isClosedMap.isClosed_range
  letI : Nonempty (pullback N.cover.map c : Scheme) :=
    ⟨Classical.choose ((pullback.snd N.cover.map c).surjective (IsLocalRing.closedPoint K))⟩
  apply finite_etale_rational_split (pullback.snd N.cover.map c)
  intro x
  obtain ⟨r, hr, hx⟩ := image_points_rational D I f y axis eta (a x)
  refine ⟨r ≫ inv a, ?_, ?_⟩
  · have hq : a ≫ pullback.snd I.projection c = pullback.snd N.cover.map c :=
      baseChangeMap_snd _ _ _ _ _
    rw [Category.assoc, ← hq, IsIso.inv_hom_id_assoc]
    exact hr
  · calc
      (r ≫ inv a) (IsLocalRing.closedPoint K) =
          inv a (r (IsLocalRing.closedPoint K)) := rfl
      _ = inv a (a x) :=
        congrArg (fun z : (pullback I.projection c : Scheme) => inv a z) hx
      _ = x := by
        have h := congrArg
          (fun k : pullback N.cover.map c ⟶ pullback N.cover.map c => k x)
          (IsIso.hom_inv_id a)
        exact h

/-- Every test line meeting the common good open has the complete
normalized cover split over a nonempty open of that line. -/
theorem line_split_on_open {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) (I : FiniteValueImage D) (N : NormalizedImage I)
    (U : GoodOpen N) (f : FreeLine X) (y : ComplexPoint X.variety) (axis : Axis)
    (hmeet : MeetsOpen (testLine f y axis) U.openSet) :
    Nonempty (SplitOnOpen N.cover.map (testLine f y axis)) := by
  letI : IsIntegral ProjectiveLine := projectiveLine_integral
  letI : Smooth P.structureMap := smoothProperComplexVariety_smooth (projectiveLineVariety P)
  letI : IsLocallyNoetherian ProjectiveLine :=
    LocallyOfFiniteType.isLocallyNoetherian P.structureMap
  let c := testLine f y axis
  let eta : Spec ProjectiveLine.functionField ⟶ ProjectiveLine :=
    ProjectiveLine.fromSpecStalk (genericPoint ProjectiveLine)
  have hgeneric : c (genericPoint ProjectiveLine) ∈ U.openSet :=
    ((genericPoint_spec ProjectiveLine).mem_open_set_iff (c ⁻¹ᵁ U.openSet).isOpen).mpr
      (by
        simp only [Set.univ_inter]
        obtain ⟨t, ht⟩ := hmeet
        exact ⟨t, ht⟩)
  have hrange : Set.range (eta ≫ c) ⊆ (U.openSet : Set (Square X)) := by
    rintro _ ⟨t, rfl⟩
    change c (eta t) ∈ U.openSet
    have ht : t = IsLocalRing.closedPoint ProjectiveLine.functionField :=
      Subsingleton.elim (α := PrimeSpectrum ProjectiveLine.functionField) _ _
    have heta : eta t = genericPoint ProjectiveLine := by
      calc
        eta t = eta (IsLocalRing.closedPoint ProjectiveLine.functionField) :=
          congrArg (fun z : PrimeSpectrum ProjectiveLine.functionField => eta z) ht
        _ = genericPoint ProjectiveLine := Scheme.fromSpecStalk_closedPoint
    rw [heta]
    exact hgeneric
  obtain ⟨m, hm, e, he⟩ := normalized_field_split D I N U f y axis eta hrange
  let q := pullback.snd N.cover.map c
  let eg : pullback q eta ≅ ∐ (fun _ : Fin m => Spec ProjectiveLine.functionField) :=
    pullbackLeftPullbackSndIso N.cover.map c eta ≪≫ e
  have heg : eg.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 (Spec ProjectiveLine.functionField)) =
      pullback.snd q eta := by
    calc
      eg.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 (Spec ProjectiveLine.functionField)) =
          (pullbackLeftPullbackSndIso N.cover.map c eta).hom ≫
            (e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 (Spec ProjectiveLine.functionField))) :=
        Category.assoc _ _ _
      _ = (pullbackLeftPullbackSndIso N.cover.map c eta).hom ≫
          pullback.snd N.cover.map (eta ≫ c) :=
        congrArg
          (fun k : pullback N.cover.map (eta ≫ c) ⟶ Spec ProjectiveLine.functionField =>
            (pullbackLeftPullbackSndIso N.cover.map c eta).hom ≫ k) he
      _ = pullback.snd q eta := pullbackLeftPullbackSndIso_hom_snd _ _ _
  obtain ⟨V, hV, ev, hev⟩ :=
    LeBrunSalamon.StandardInputs.finite_generic_trivialization_spreads q m eg heg
  let eV : pullback N.cover.map (V.ι ≫ c) ≅ ∐ (fun _ : Fin m => V.toScheme) :=
    (pullbackLeftPullbackSndIso N.cover.map c V.ι).symm ≪≫ ev
  refine ⟨{
    openSet := V
    nonempty := ⟨genericPoint ProjectiveLine, hV⟩
    sheets := m
    positiveSheets := hm
    identification := eV
    overSource := ?_ }⟩
  change eV.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 V.toScheme) =
    pullback.snd N.cover.map (V.ι ≫ c)
  calc
    eV.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 V.toScheme) =
        (pullbackLeftPullbackSndIso N.cover.map c V.ι).inv ≫
          (ev.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 V.toScheme)) :=
      Category.assoc _ _ _
    _ = (pullbackLeftPullbackSndIso N.cover.map c V.ι).inv ≫
        pullback.snd q V.ι :=
      congrArg (fun k : pullback q V.ι ⟶ V.toScheme =>
        (pullbackLeftPullbackSndIso N.cover.map c V.ι).inv ≫ k) hev
    _ = pullback.snd N.cover.map (V.ι ≫ c) :=
      pullbackLeftPullbackSndIso_inv_snd_snd _ _ _

end LeBrunSalamon.Construction.Descent.GenericSheets

namespace LeBrunSalamon.Construction.Descent

/-- SOURCE des:component-section and des:all-sheets. Uses both vector
lifts, constancy of functions on EACH proper integral dominating source
component, and the finite-image embedding in a line bundle. It does NOT
assume that these components have rational points over C(P1). -/
theorem allSheets_split {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) (I : FiniteValueImage D) (N : NormalizedImage I)
    (U : GoodOpen N) (H : CoveringFamily X) : AllSheetsSplit N U H := by
  intro t y axis hmeet
  exact GenericSheets.line_split_on_open D I N U (H.lineAt t) y axis hmeet

end LeBrunSalamon.Construction.Descent

namespace LeBrunSalamon.Refinement

open LeBrunSalamon.Construction



end LeBrunSalamon.Refinement

end

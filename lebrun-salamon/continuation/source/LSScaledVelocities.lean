import LSBoundedLines
import LSFiniteTypeDominance

/-!
## Scalar parameters for the actual universal line velocity

The normalized source tangent spans its actual one-dimensional fibre.
An affine-line scalar parameter therefore covers every selected velocity
without a reparametrization theorem. The source below is the literal
bounded fixed-node Hom fibre times A1, and all coordinates are pullbacks
of its actual universal velocity morphism.

Source preparation only; no compiler has been invoked.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.GlobalCoordinates

open DirectionCones SectionAlgebra

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

@[reassoc] theorem affineMap_comp (f : A →ₐ[ℂ] B)
    {R : Type} [CommRing R] [Algebra ℂ R] (g : B →ₐ[ℂ] R) :
    affineMap g ≫ affineMap f = affineMap (g.comp f) := by
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

theorem specPoint_affineMap (f : A →ₐ[ℂ] ℂ)
    (hf : affineMap f ≫ affineBaseMap A = 𝟙 ComplexBase) :
    GlobalVelocity.specPoint (affineMap f) hf = f := by
  ext a
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((affineMap f).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = f a
  have h := congrArg (fun k : CommRingCat.of A ⟶ Γ(ComplexBase, ⊤) => k a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f.toRingHom))
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (f a) =
    (affineMap f).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) at h
  rw [← h]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) (f a)

/-- Equality of actual affine-valued points preserves their coefficient map.
The proof parameters are handled dependently before evaluating the map. -/
theorem specPoint_congr {q q' : ComplexBase ⟶ Spec (CommRingCat.of A)}
    (h : q = q')
    (hq : q ≫ affineBaseMap A = 𝟙 ComplexBase)
    (hq' : q' ≫ affineBaseMap A = 𝟙 ComplexBase) :
    GlobalVelocity.specPoint q hq = GlobalVelocity.specPoint q' hq' := by
  cases h
  rfl

/-- The actual scalar evaluation of a global function at a complex point. -/
def evaluation {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (t : PointsOver ComplexBase (𝟙 ComplexBase) Y sY) : Functions sY ⊤ →ₐ[ℂ] ℂ where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp t.val.appTop.hom
  commutes' := by
    intro c
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (t.val.appTop (complexConstants sY c)) = c
    rw [complexConstants_naturality t.val (𝟙 ComplexBase) sY t.property,
      complexConstants_apply_top]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) c

theorem evaluation_function {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (t : PointsOver ComplexBase (𝟙 ComplexBase) Y sY) (a : Functions sY ⊤) :
    t.val.appTop a = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (evaluation t a) :=
  (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) (t.val.appTop a)).symm

theorem point_mem_basicOpen {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (t : PointsOver ComplexBase (𝟙 ComplexBase) Y sY) (a : Functions sY ⊤) :
    t.val (IsLocalRing.closedPoint ℂ) ∈ Y.basicOpen a ↔ evaluation t a ≠ 0 := by
  change IsLocalRing.closedPoint ℂ ∈ t.val ⁻¹ᵁ Y.basicOpen a ↔ _
  rw [Scheme.preimage_basicOpen_top, evaluation_function, basicOpen_eq_of_affine,
    PrimeSpectrum.mem_basicOpen]
  have hp : IsLocalRing.closedPoint ℂ = (⊥ : PrimeSpectrum ℂ) := Subsingleton.elim _ _
  simp only [hp, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot]

/-- The full comorphism into an affine scheme, defined for an arbitrary
source and retaining its specified complex scalar structure. -/
def comorphism {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (g : Y ⟶ Spec (CommRingCat.of A)) (hg : g ≫ affineBaseMap A = sY) :
    A →ₐ[ℂ] Functions sY ⊤ :=
  (onFunctionsTop g hg).comp (GlobalVelocity.specFunctions A)

theorem comorphism_apply {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (g : Y ⟶ Spec (CommRingCat.of A)) (hg : g ≫ affineBaseMap A = sY) (a : A) :
    comorphism g hg a = g.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := rfl

theorem comorphism_precompose {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Spec (CommRingCat.of A)) (hg : g ≫ affineBaseMap A = sY)
    (k : Z ⟶ Y) (hk : k ≫ sY = sZ) :
    comorphism (k ≫ g) (by rw [Category.assoc, hg, hk]) =
      (onFunctionsTop k hk).comp (comorphism g hg) := by
  ext a
  exact congrArg (fun f : Γ(Spec (CommRingCat.of A), ⊤) ⟶ Γ(Z, ⊤) =>
    f ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) (Scheme.Hom.comp_appTop k g)

theorem comorphism_affineMap {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (g : Y ⟶ Spec (CommRingCat.of B)) (hg : g ≫ affineBaseMap B = sY)
    (f : A →ₐ[ℂ] B) :
    comorphism (g ≫ affineMap f) (by rw [Category.assoc, affineMap_overC, hg]) =
      (comorphism g hg).comp f := by
  ext a
  change g.appTop ((affineMap f).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
      g.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (f a))
  congr 1
  exact (congrArg (fun k : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of B), ⊤) => k a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f.toRingHom))).symm

theorem evaluation_comorphism {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (g : Y ⟶ Spec (CommRingCat.of A)) (hg : g ≫ affineBaseMap A = sY)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) Y sY) :
    (evaluation t).comp (comorphism g hg) =
      GlobalVelocity.specPoint (t.val ≫ g) (by rw [Category.assoc, hg, t.property]) := rfl

variable {I : Type} [Fintype I]

def map {Y : Scheme} (sY : Y ⟶ ComplexBase) (v : I → Functions sY ⊤) :
    Y ⟶ affineSpace I := GlobalVelocity.toSpec (MvPolynomial.aeval v)

@[reassoc] theorem map_overC {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (v : I → Functions sY ⊤) : map sY v ≫ affineBaseMap (MvPolynomial I ℂ) = sY :=
  GlobalVelocity.toSpec_overC _

theorem map_X {Y : Scheme} (sY : Y ⟶ ComplexBase) (v : I → Functions sY ⊤) (i : I) :
    (map sY v).appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I ℂ))).inv
      (MvPolynomial.X i)) = v i := by
  rw [map, GlobalVelocity.toSpec_function, MvPolynomial.aeval_X]

/-- Equality of complete complex-valued scheme maps follows from their
coordinate functions, before passing to topological supports. -/
theorem map_point {Y : Scheme} (sY : Y ⟶ ComplexBase) (v : I → Functions sY ⊤)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) Y sY) :
    t.val ≫ map sY v = coordinatePoint (fun i => evaluation t (v i)) := by
  have hbase : affineBaseMap ℂ = 𝟙 ComplexBase := by
    change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = _
    simpa using Spec.map_id (CommRingCat.of ℂ)
  have ht : t.val ≫ sY = affineBaseMap ℂ := t.property.trans hbase.symm
  rw [map, GlobalVelocity.toSpec_precompose (MvPolynomial.aeval v) t.val ht]
  have h : (onFunctionsTop t.val ht).comp (MvPolynomial.aeval v) =
      (GlobalVelocity.specFunctions ℂ).comp (MvPolynomial.aeval (fun i => evaluation t (v i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, onFunctionsTop_apply,
      GlobalVelocity.specFunctions_apply]
    exact evaluation_function t (v i)
  rw [h, GlobalVelocity.toSpec_specFunctions]
  rfl

theorem evaluation_precompose {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) Y sY) (a : Functions sZ ⊤) :
    evaluation t (onFunctionsTop g hg a) =
      evaluation (⟨t.val ≫ g, by rw [Category.assoc, hg, t.property]⟩ :
        PointsOver ComplexBase (𝟙 ComplexBase) Z sZ) a := rfl

/-- Complex-point coverage transfers dominance from any actual
finite-type source. This uses the density of closed complex points,
without reducing or replacing either parameter scheme. -/
theorem denseRange_of_point_coverage {Y Z T : Scheme}
    (sY : Y ⟶ ComplexBase) [LocallyOfFiniteType sY]
    (sT : T ⟶ ComplexBase) (a : Y ⟶ Z) (ha : DenseRange (fun y => a y))
    (f : T ⟶ Z)
    (hcover : ∀ p : PointsOver ComplexBase (𝟙 ComplexBase) Y sY,
      ∃ q : PointsOver ComplexBase (𝟙 ComplexBase) T sT, q.val ≫ f = p.val ≫ a) :
    DenseRange (fun t => f t) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨z, hzU, y, rfl⟩ := ha.inter_open_nonempty U hU hUne
  let V : Y.Opens := a ⁻¹ᵁ (⟨U, hU⟩ : Z.Opens)
  obtain ⟨p, hp, hpV⟩ := RelativeGenericSmoothness.exists_point_in_nonempty_open sY V ⟨y, hzU⟩
  obtain ⟨q, hq⟩ := hcover ⟨p, hp⟩
  refine ⟨f (q.val (IsLocalRing.closedPoint ℂ)), ?_, q.val (IsLocalRing.closedPoint ℂ), rfl⟩
  have hvalue := congrArg (fun g : ComplexBase ⟶ Z => g (IsLocalRing.closedPoint ℂ)) hq
  exact hvalue.symm ▸ hpV

/-- Polynomial affine space has all the prescribed actual tangent
coordinates. The lift is the literal epsilon translation of each Xi. -/
theorem polynomialTangent_coordinates (q : MvPolynomial I ℂ →ₐ[ℂ] ℂ) (v : I → ℂ) :
    ∃ E : Infinitesimal.Tangent (MvPolynomial I ℂ) q,
      ∀ i, E.val (MvPolynomial.X i) = v i := by
  let F : MvPolynomial I ℂ →ₐ[ℂ] Infinitesimal.Dual := MvPolynomial.aeval
    (fun i => algebraMap ℂ Infinitesimal.Dual (q (MvPolynomial.X i)) +
      Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (v i))
  have hF : Infinitesimal.residue.comp F = q := by
    apply MvPolynomial.algHom_ext
    intro i
    change Infinitesimal.residue (F (MvPolynomial.X i)) = q (MvPolynomial.X i)
    simpa only [F, MvPolynomial.aeval_X] using
      (Infinitesimal.residue_normalForm (q (MvPolynomial.X i)) (v i))
  obtain ⟨E, hE⟩ := (Infinitesimal.tangentToDual_bijective q).2 ⟨F, hF⟩
  refine ⟨E, ?_⟩
  intro i
  have he := congrArg
    (fun f : {f : MvPolynomial I ℂ →ₐ[ℂ] Infinitesimal.Dual // Infinitesimal.residue.comp f = q} =>
      Infinitesimal.linearCoefficient (f.val (MvPolynomial.X i))) hE
  change Infinitesimal.linearCoefficient
    (algebraMap ℂ Infinitesimal.Dual (q (MvPolynomial.X i)) +
      Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (E.val (MvPolynomial.X i))) =
        Infinitesimal.linearCoefficient (F (MvPolynomial.X i)) at he
  simpa only [F, MvPolynomial.aeval_X, Infinitesimal.linearCoefficient_normalForm] using he

end LeBrunSalamon.Construction.Lines.GlobalCoordinates

namespace LeBrunSalamon.Construction.Lines.ScaledVelocities

open DirectionCones SectionAlgebra VelocityCoordinates GlobalCoordinates

variable {n : ℕ} (X : ContactFanoManifold n)
variable (H : HomSpacePresentation P X.variety)
variable (D : HomDegree.Open P marking X.variety H X.contact.sequence.line 1)
variable (x : ComplexPoint X.variety) (C : GlobalVelocity.TargetChart X.variety x)

abbrev Index := Fin (dimension (n := n) + 1)
abbrev scalarLine : Scheme := Spec (CommRingCat.of (Polynomial ℂ))
abbrev scalarToC : scalarLine ⟶ ComplexBase := affineBaseMap (Polynomial ℂ)

abbrev parameter : Scheme := pullback (FixedFreeParameter.toC X H D x) scalarToC
def toBounded : parameter X H D x ⟶ FixedFreeParameter.parameter X H D x := pullback.fst _ _
def toScalar : parameter X H D x ⟶ scalarLine := pullback.snd _ _
def toC : parameter X H D x ⟶ ComplexBase :=
  toBounded X H D x ≫ FixedFreeParameter.toC X H D x

@[reassoc] theorem toScalar_overC : toScalar X H D x ≫ scalarToC = toC X H D x :=
  pullback.condition.symm

instance toC_finiteType : LocallyOfFiniteType (toC X H D x) := by
  dsimp [toC, toBounded, scalarToC]
  infer_instance

instance toC_quasiCompact : QuasiCompact (toC X H D x) := by
  dsimp [toC, toBounded, scalarToC]
  infer_instance

def asFixedHom : PointsOver (parameter X H D x) (toC X H D x)
    (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x) :=
  ⟨toBounded X H D x ≫ (FixedFreeParameter.asFixedHom X H D x).val, by
    rw [Category.assoc, (FixedFreeParameter.asFixedHom X H D x).property]; rfl⟩

def velocity : parameter X H D x ⟶ AffineVelocity.tangentScheme C.evaluation :=
  (asFixedHom X H D x).val ≫
    GlobalVelocity.homVelocity P marking H x (PolynomialSourceLift.atMarking marking) C

@[reassoc] theorem velocity_overC :
    velocity X H D x C ≫ AffineVelocity.tangentSchemeToC C.evaluation = toC X H D x := by
  rw [velocity, Category.assoc, GlobalVelocity.homVelocity_overC]
  exact (asFixedHom X H D x).property

def unscaledFunctions : MvPolynomial (Index (n := n)) ℂ →ₐ[ℂ] Functions (toC X H D x) ⊤ :=
  (GlobalCoordinates.comorphism (velocity X H D x C) (velocity_overC X H D x C)).comp
    (ambientPolynomial C.evaluation (ContactVelocityTarget.image X x C)
      (contactCoordinateBasis X x C))

def scalar : Functions (toC X H D x) ⊤ :=
  GlobalCoordinates.comorphism (toScalar X H D x) (toScalar_overC X H D x) Polynomial.X

def coordinates (i : Index (n := n)) : Functions (toC X H D x) ⊤ :=
  scalar X H D x * unscaledFunctions X H D x C (MvPolynomial.X i)

def morphism : parameter X H D x ⟶ affineSpace (Index (n := n)) :=
  GlobalCoordinates.map (toC X H D x) (coordinates X H D x C)

@[reassoc] theorem morphism_overC :
    morphism X H D x C ≫ affineBaseMap (MvPolynomial (Index (n := n)) ℂ) = toC X H D x :=
  GlobalCoordinates.map_overC _ _

def scalarPoint (c : ℂ) : ComplexBase ⟶ scalarLine := affineMap (Polynomial.aeval c)

@[reassoc] theorem scalarPoint_overC (c : ℂ) : scalarPoint c ≫ scalarToC = 𝟙 ComplexBase := by
  change affineMap (Polynomial.aeval c) ≫ affineBaseMap (Polynomial ℂ) = _
  rw [affineMap_overC]
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = _
  simpa using Spec.map_id (CommRingCat.of ℂ)

def center (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map) (c : ℂ) :
    PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x) (toC X H D x) :=
  ⟨pullback.lift (FixedFreeParameter.center X H D x f hf).val (scalarPoint c)
      ((FixedFreeParameter.center X H D x f hf).property.trans (scalarPoint_overC c).symm), by
    simp only [toC, toBounded, ← Category.assoc, pullback.lift_fst,
      (FixedFreeParameter.center X H D x f hf).property]⟩

@[reassoc] theorem center_asFixedHom (f : FreeLine X)
    (hf : marking.map ≫ f.curve.map = x.map) (c : ℂ) :
    (center X H D x f hf c).val ≫ (asFixedHom X H D x).val =
      (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val := by
  simp only [center, asFixedHom, toBounded, ← Category.assoc, pullback.lift_fst,
    FixedFreeParameter.center_asFixedHom]

@[reassoc] theorem center_toScalar (f : FreeLine X)
    (hf : marking.map ≫ f.curve.map = x.map) (c : ℂ) :
    (center X H D x f hf c).val ≫ toScalar X H D x = scalarPoint c := by
  simp only [center, toScalar, pullback.lift_snd]

theorem point_is_freeLine
    (t : PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x) (toC X H D x)) :
    ∃ (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map),
      t.val ≫ (asFixedHom X H D x).val =
        (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val := by
  let q : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedFreeParameter.parameter X H D x) (FixedFreeParameter.toC X H D x) :=
    ⟨t.val ≫ toBounded X H D x, by rw [Category.assoc]; exact t.property⟩
  obtain ⟨f, hf, he⟩ := FixedFreeParameter.point_is_freeLine X H D x q
  exact ⟨f, hf, by simpa only [q, asFixedHom, Category.assoc] using he⟩

/-- The original normalized node vector, retained as an element of the
original contact plane. -/
def nodeVector (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map) : contactPlane X x :=
  ⟨nodeDifferential f x hf (SourceTangent.sourceVector marking),
    ContactPositive.nodeDifferential_mem_contactPlane f x hf (SourceTangent.sourceVector marking)⟩

theorem unscaledFunctions_point
    (t : PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x) (toC X H D x))
    (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map)
    (ht : t.val ≫ (asFixedHom X H D x).val =
      (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val) :
    (GlobalCoordinates.evaluation t).comp (unscaledFunctions X H D x C) =
      MvPolynomial.aeval (contactFrame X x C (nodeVector X x f hf)) := by
  let q := GlobalVelocity.specPoint (t.val ≫ velocity X H D x C)
    (by
      change (t.val ≫ velocity X H D x C) ≫
        AffineVelocity.tangentSchemeToC C.evaluation = 𝟙 ComplexBase
      rw [Category.assoc, velocity_overC, t.property])
  have hv : AffineVelocity.tangentPointEquiv C.evaluation q =
      IntrinsicTangent.chartEvaluation C (nodeVector X x f hf).val := by
    change HomVelocityValue.value H x C
      (⟨t.val ≫ (asFixedHom X H D x).val, by
        rw [Category.assoc, (asFixedHom X H D x).property, t.property]⟩ :
          PointsOver ComplexBase (𝟙 ComplexBase)
            (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x)) = _
    have he : (⟨t.val ≫ (asFixedHom X H D x).val, by
        rw [Category.assoc, (asFixedHom X H D x).property, t.property]⟩ :
          PointsOver ComplexBase (𝟙 ComplexBase)
            (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x)) =
        HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf := Subtype.ext ht
    rw [he]
    exact HomVelocityValue.value_fixedCenter H f x hf C
  unfold unscaledFunctions
  rw [← AlgHom.comp_assoc, GlobalCoordinates.evaluation_comorphism]
  exact ambientPolynomial_point C.evaluation (ContactVelocityTarget.image X x C)
    (contactCoordinateBasis X x C) q
    (ContactVelocityTarget.imageEquiv X x C (nodeVector X x f hf)) hv

theorem coordinates_point
    (t : PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x) (toC X H D x))
    (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map)
    (ht : t.val ≫ (asFixedHom X H D x).val =
      (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val) :
    (fun i => GlobalCoordinates.evaluation t (coordinates X H D x C i)) =
      contactFrame X x C (GlobalCoordinates.evaluation t (scalar X H D x) • nodeVector X x f hf) := by
  funext i
  have h := AlgHom.congr_fun (unscaledFunctions_point X H D x C t f hf ht) (MvPolynomial.X i)
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X] at h
  simp only [coordinates, map_mul, h, map_smul, Pi.smul_apply, smul_eq_mul]

theorem scalar_center (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map) (c : ℂ) :
    GlobalCoordinates.evaluation (center X H D x f hf c) (scalar X H D x) = c := by
  have he := AlgHom.congr_fun
    (GlobalCoordinates.evaluation_comorphism (toScalar X H D x) (toScalar_overC X H D x)
      (center X H D x f hf c)) Polynomial.X
  change GlobalCoordinates.evaluation (center X H D x f hf c) (scalar X H D x) =
    GlobalVelocity.specPoint ((center X H D x f hf c).val ≫ toScalar X H D x)
      (by rw [Category.assoc, toScalar_overC, (center X H D x f hf c).property]) Polynomial.X at he
  have hpoint := GlobalCoordinates.specPoint_congr
    (center_toScalar X H D x f hf c)
    (by rw [Category.assoc, toScalar_overC, (center X H D x f hf c).property])
    (scalarPoint_overC c)
  exact he.trans ((AlgHom.congr_fun hpoint Polynomial.X).trans
    ((AlgHom.congr_fun
      (GlobalCoordinates.specPoint_affineMap (Polynomial.aeval c)
        (scalarPoint_overC c)) Polynomial.X).trans (by
          simp only [Polynomial.aeval_X])))

theorem center_coordinates (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map) (c : ℂ) :
    (fun i => GlobalCoordinates.evaluation (center X H D x f hf c) (coordinates X H D x C i)) =
      contactFrame X x C (c • nodeVector X x f hf) := by
  rw [coordinates_point X H D x C _ f hf (center_asFixedHom X H D x f hf c), scalar_center]

@[reassoc] theorem center_morphism (f : FreeLine X)
    (hf : marking.map ≫ f.curve.map = x.map) (c : ℂ) :
    (center X H D x f hf c).val ≫ morphism X H D x C =
      coordinatePoint (contactFrame X x C (c • nodeVector X x f hf)) := by
  rw [morphism, GlobalCoordinates.map_point, center_coordinates]

/-- The actual tangent line is spanned by the already normalized source
vector. This converts every selected velocity into our actual scalar family. -/
theorem sourceVector_spans (t : Fiber (tangentSheaf P.structureMap) marking.map) :
    ∃ c : ℂ, c • SourceTangent.sourceVector marking = t := by
  exact exists_smul_eq_of_finrank_eq_one
    (fiber_dimension (intrinsicTangentBundle (projectiveLineVariety P)) marking.map)
    (SourceTangent.sourceVector_ne_zero marking) t

theorem selectedVector_covered (v : contactPlane X x)
    (hv : IsSelectedVector (fun _ : FreeLine X => True) x v) :
    ∃ t : PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x) (toC X H D x),
      t.val ≫ morphism X H D x C = coordinatePoint (contactFrame X x C v) := by
  obtain ⟨f, _hf, hfx, p, hp⟩ := hv
  obtain ⟨c, hc⟩ := sourceVector_spans p
  have hvec : c • nodeVector X x f hfx = v := by
    apply Subtype.ext
    change c • nodeDifferential f x hfx (SourceTangent.sourceVector marking) = v.val
    rw [← map_smul, hc]
    exact hp
  exact ⟨center X H D x f hfx c, by rw [center_morphism, hvec]⟩

theorem selectedVector_coordinate_covered (v : contactPlane X x)
    (hv : IsSelectedVector (fun _ : FreeLine X => True) x v) :
    ∃ t : PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x) (toC X H D x),
      (fun i => GlobalCoordinates.evaluation t (coordinates X H D x C i)) = contactFrame X x C v := by
  obtain ⟨f, _hf, hfx, p, hp⟩ := hv
  obtain ⟨c, hc⟩ := sourceVector_spans p
  have hvec : c • nodeVector X x f hfx = v := by
    apply Subtype.ext
    change c • nodeDifferential f x hfx (SourceTangent.sourceVector marking) = v.val
    rw [← map_smul, hc]
    exact hp
  exact ⟨center X H D x f hfx c, by rw [center_coordinates, hvec]⟩

end LeBrunSalamon.Construction.Lines.ScaledVelocities

end

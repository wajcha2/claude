import LSIntrinsicVelocity

/-!
## Relative generic smoothness on the actual source open

For the actual dominant locally finitely presented morphism between integral
schemes over a characteristic-zero field, its relative smooth locus contains
the source generic point. It meets every supplied nonempty source open.
The complex finite-type wrapper constructs that intersection, its smooth
restricted morphism, and an actual complex point over the stated base maps.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory

namespace LeBrunSalamon.Construction.Lines.RelativeGenericSmoothness

universe u

variable {X Y : AlgebraicGeometry.Scheme.{u}}

open AlgebraicGeometry

/-- The actual base-field map into a stalk, obtained from the structural
morphism, global sections of the spectrum, and the germ map. -/
def baseToStalk {K : Type u} [Field K]
    (sY : Y ⟶ Spec (CommRingCat.of K)) (y : Y) :
    K →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ ⊤ y (by trivial)).hom.comp
    (sY.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

/-- Dominance carries the generic point to the generic point.
Source: Stacks Project, Tag 0CC1; this proof uses the existing topology API. -/
lemma map_genericPoint_of_dominant
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have h : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec X).image f.continuous
  exact h.eq (genericPoint_spec Y)

set_option backward.isDefEq.respectTransparency false in
/-- A dominant locally finitely presented morphism between integral schemes
over a characteristic-zero field is smooth at the source generic point.

The theorem needs only an actual structural map on the target: its purpose is
to give the target function field characteristic zero. The later finite-type
complex wrapper explicitly includes both structural maps and their triangle.

Source: Stacks Project, Tag 07ND, applied on affine neighbourhoods, together
with Tag 0CC1. The body works directly with the actual generic stalk map.
-/
theorem genericPoint_mem_smoothLocus_of_dominant_charZero
    {K : Type u} [Field K] [CharZero K]
    [IsIntegral X] [IsIntegral Y]
    (sY : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y)
    [IsDominant f] [LocallyOfFinitePresentation f] :
    genericPoint X ∈ f.smoothLocus := by
  have hη : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_of_dominant f
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [hη]
    exact Field.toIsField Y.functionField
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := hfield.toField
  haveI : CharZero (Y.presheaf.stalk (f (genericPoint X))) :=
    charZero_of_injective_ringHom (baseToStalk sY (f (genericPoint X))).injective
  have := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(f.stalkMap (genericPoint X)).hom]
  exact Algebra.FormallySmooth.of_perfectField

/-- Every supplied nonempty source open meets the relative smooth locus.
In the manuscript application, `U` is the independently constructed actual
nonorthogonality open. This theorem does not construct `U` or prove its
nonemptiness, and it does not manufacture the required dominance hypothesis. -/
theorem nonempty_inter_smoothLocus_of_dominant_charZero
    {K : Type u} [Field K] [CharZero K]
    [IsIntegral X] [IsIntegral Y]
    (sY : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y)
    [IsDominant f] [LocallyOfFinitePresentation f]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    ((U ⊓ f.smoothLocus : X.Opens) : Set X).Nonempty := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  exact ⟨genericPoint X, hηU,
    genericPoint_mem_smoothLocus_of_dominant_charZero sY f⟩

/-- The restriction to an actual source open contained in the smooth locus
is smooth. This follows from mathlib's open-immersion compatibility theorem. -/
theorem smooth_restrict_of_le_smoothLocus
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (W : X.Opens) (hW : W ≤ f.smoothLocus) :
    Smooth (W.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq W.ι f]
  apply top_unique
  intro x _
  exact hW x.property

/-- A nonempty source open in a scheme locally of finite type over an
algebraically closed field contains an actual rational point over that field.
Source: Stacks Project, Tag 0478, and algebraic closedness of the base field. -/
theorem exists_point_in_nonempty_open
    {K : Type u} [Field K] [IsAlgClosed K]
    (sX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType sX]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    ∃ p : Spec (CommRingCat.of K) ⟶ X,
      p ≫ sX = 𝟙 _ ∧ p (IsLocalRing.closedPoint K) ∈ U := by
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  obtain ⟨x, hxU, hxclosed⟩ :=
    nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  refine ⟨pointOfClosedPoint sX x hxclosed,
    pointOfClosedPoint_comp sX x hxclosed, ?_⟩
  have hp : pointOfClosedPoint sX x hxclosed (IsLocalRing.closedPoint K) = x :=
    pointOfClosedPoint_apply sX x hxclosed (IsLocalRing.closedPoint K)
  exact Eq.mpr (congrArg (fun y : X => y ∈ (U : Set X)) hp) hxU

/-- Exact finite-type complex-scheme interface for the next manuscript step.

The structure maps, the morphism, dominance, the finite-type hypotheses, and
the nonempty open are all actual data/hypotheses. Finite type is represented
by mathlib's two classes `LocallyOfFiniteType` and `QuasiCompact`.

The returned source open is constructed as `U ⊓ f.smoothLocus`. It carries an
actual complex point and the restriction of the actual morphism is smooth.
No statement about smoothness over the whole inverse image of a base open is
made. Quasi-compactness is not needed for this local conclusion, but is kept
in this wrapper to match the requested bounded finite-type interface.
-/
theorem finiteTypeComplex_exists_smooth_source_open_point
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ Spec (CommRingCat.of ℂ))
    (sY : Y ⟶ Spec (CommRingCat.of ℂ))
    (f : X ⟶ Y) (hf : f ≫ sY = sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX]
    [LocallyOfFiniteType sY] [QuasiCompact sY]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    ∃ (W : X.Opens) (q : Spec (CommRingCat.of ℂ) ⟶ W),
      W ≤ U ∧ (W : Set X).Nonempty ∧ Smooth (W.ι ≫ f) ∧
      q ≫ W.ι ≫ sX = 𝟙 _ ∧ q ≫ W.ι ≫ f ≫ sY = 𝟙 _ := by
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  letI : LocallyOfFinitePresentation f := inferInstance
  let W : X.Opens := U ⊓ f.smoothLocus
  have hW : (W : Set X).Nonempty :=
    nonempty_inter_smoothLocus_of_dominant_charZero sY f U hU
  have htop : ((⊤ : W.toScheme.Opens) : Set W.toScheme).Nonempty := by
    obtain ⟨x, hx⟩ := hW
    exact ⟨⟨x, hx⟩, trivial⟩
  obtain ⟨q, hq, _⟩ :=
    exists_point_in_nonempty_open (W.ι ≫ sX) ⊤ htop
  refine ⟨W, q, inf_le_left, hW,
    smooth_restrict_of_le_smoothLocus f W inf_le_right, hq, ?_⟩
  simpa only [Category.assoc, hf] using hq

end LeBrunSalamon.Construction.Lines.RelativeGenericSmoothness

end

/-!
## Formal smoothness gives surjectivity of the actual point differential

This bridge uses the project's actual ring C[epsilon]/(epsilon^2), its
residue map, and its normalized equivalence between derivations and
dual-number points. Formal smoothness is the standard mathlib property
of the actual comorphism. The proof constructs a lift of the actual
point; no tangent-surjectivity conclusion is supplied as a hypothesis.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.SmoothTangent

open Infinitesimal

/-- The actual residue map is surjective by its original scalar section. -/
theorem residue_surjective : Function.Surjective residue := by
  intro c
  exact ⟨algebraMap ℂ Dual c, residue.commutes c⟩

/-- Every element in the actual residue kernel is an epsilon multiple,
so the product of any two such elements vanishes. -/
theorem residue_kernel_square_zero :
    (RingHom.ker residue.toRingHom) ^ 2 = (⊥ : Ideal Dual) := by
  apply le_antisymm
  · rw [pow_two, Ideal.mul_le]
    intro u hu v hv
    apply Ideal.mem_bot.mpr
    have hu0 : residue u = 0 := hu
    have hv0 : residue v = 0 := hv
    have hu' : u = epsilon * algebraMap ℂ Dual (linearCoefficient u) :=
      (dual_normalForm_reconstruct u).trans (by rw [hu0, map_zero, zero_add])
    have hv' : v = epsilon * algebraMap ℂ Dual (linearCoefficient v) :=
      (dual_normalForm_reconstruct v).trans (by rw [hv0, map_zero, zero_add])
    calc
      u * v = (epsilon * algebraMap ℂ Dual (linearCoefficient u)) *
          (epsilon * algebraMap ℂ Dual (linearCoefficient v)) :=
        congrArg₂ (fun a b : Dual => a * b) hu' hv'
      _ = epsilon ^ 2 * (algebraMap ℂ Dual (linearCoefficient u) *
          algebraMap ℂ Dual (linearCoefficient v)) := by ring
      _ = 0 := by rw [epsilon_square, zero_mul]
  · exact bot_le

theorem residue_kernel_nilpotent : IsNilpotent (RingHom.ker residue.toRingHom) :=
  ⟨2, residue_kernel_square_zero⟩

section FormalSmoothness

variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra ℂ A] [Algebra ℂ B]

/-- Lift a genuine dual-number square for the actual comorphism f.
The A-action on Dual is the prescribed infinitesimal target point tau;
the A-action on C is its residue p composed with f. -/
theorem exists_dual_lift_of_formallySmooth
    (f : A →ₐ[ℂ] B) (hf : f.toRingHom.FormallySmooth)
    (p : B →ₐ[ℂ] ℂ) (tau : A →ₐ[ℂ] Dual)
    (htau : residue.comp tau = p.comp f) :
    ∃ sigma : B →ₐ[ℂ] Dual,
      residue.comp sigma = p ∧ sigma.comp f = tau := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : Algebra.FormallySmooth A B := hf
  letI : Algebra A Dual := tau.toRingHom.toAlgebra
  letI : Algebra A ℂ := (p.comp f).toRingHom.toAlgebra
  let pointOverA : B →ₐ[A] ℂ :=
    { toRingHom := p.toRingHom
      commutes' := fun _ => rfl }
  let residueOverA : Dual →ₐ[A] ℂ :=
    { toRingHom := residue.toRingHom
      commutes' := fun a => AlgHom.congr_fun htau a }
  have hsurj : Function.Surjective residueOverA := residue_surjective
  have hnil : IsNilpotent (RingHom.ker residueOverA.toRingHom) :=
    residue_kernel_nilpotent
  let liftOverA : B →ₐ[A] Dual :=
    Algebra.FormallySmooth.liftOfSurjective pointOverA residueOverA hsurj hnil
  let sigma : B →ₐ[ℂ] Dual :=
    { toRingHom := liftOverA.toRingHom
      commutes' := by
        intro c
        change liftOverA (algebraMap ℂ B c) = algebraMap ℂ Dual c
        rw [← f.commutes c, ← tau.commutes c]
        exact liftOverA.commutes (algebraMap ℂ A c) }
  refine ⟨sigma, ?_, ?_⟩
  · apply AlgHom.ext
    intro b
    exact Algebra.FormallySmooth.liftOfSurjective_apply
      pointOverA residueOverA hsurj hnil b
  · apply AlgHom.ext
    intro a
    exact liftOverA.commutes a

/-- The actual point differential of a formally smooth comorphism is
surjective. The preimage is obtained from an actual dual-number lift,
with both its center and its restriction to A verified. -/
theorem tangentMap_surjective_of_formallySmooth
    (f : A →ₐ[ℂ] B) (hf : f.toRingHom.FormallySmooth)
    (p : B →ₐ[ℂ] ℂ) :
    Function.Surjective (Infinitesimal.tangentMap f p) := by
  intro D
  obtain ⟨sigma, hresidue, hrestrict⟩ :=
    exists_dual_lift_of_formallySmooth f hf p
      (tangentToDual (p.comp f) D) (tangentToDual_residue (p.comp f) D)
  let pointLift : {sigma : B →ₐ[ℂ] Dual // residue.comp sigma = p} :=
    ⟨sigma, hresidue⟩
  obtain ⟨E, hE⟩ := (tangentToDual_bijective p).2 pointLift
  have hEdual : tangentToDual p E = sigma := congrArg Subtype.val hE
  refine ⟨E, ?_⟩
  apply (tangentToDual_bijective (p.comp f)).1
  apply Subtype.ext
  change tangentToDual (p.comp f) (Infinitesimal.tangentMap f p E) =
    tangentToDual (p.comp f) D
  rw [tangentToDual_natural, hEdual]
  exact hrestrict

/-- Smoothness of the actual ring comorphism implies surjectivity of its
actual point differential, through its standard formal-smoothness property. -/
theorem tangentMap_surjective_of_smooth
    (f : A →ₐ[ℂ] B) (hf : f.toRingHom.Smooth)
    (p : B →ₐ[ℂ] ℂ) :
    Function.Surjective (Infinitesimal.tangentMap f p) :=
  tangentMap_surjective_of_formallySmooth f hf.formallySmooth p

/-- The same bridge in the usual compatible algebra-tower formulation.
The comorphism is the scalar map of the original A-algebra B. -/
theorem tangentMap_surjective_of_formallySmooth_algebra
    [Algebra A B] [IsScalarTower ℂ A B] [Algebra.FormallySmooth A B]
    (p : B →ₐ[ℂ] ℂ) :
    Function.Surjective
      (Infinitesimal.tangentMap (IsScalarTower.toAlgHom ℂ A B) p) := by
  apply tangentMap_surjective_of_formallySmooth
  exact RingHom.formallySmooth_algebraMap.mpr inferInstance

end FormalSmoothness

section SchemeSmoothness

variable {A B : Type} [CommRing A] [CommRing B]
variable [Algebra ℂ A] [Algebra ℂ B]

/-- Smoothness of the actual affine scheme morphism yields surjectivity
of its actual point differential. The hypothesis concerns `affineMap f`
itself, and is converted to smoothness of that same comorphism by `Spec_iff`.
The universe matches the project's actual `DirectionCones.affineMap`. -/
theorem tangentMap_surjective_of_scheme_smooth
    (f : A →ₐ[ℂ] B) [AlgebraicGeometry.Smooth (DirectionCones.affineMap f)]
    (p : B →ₐ[ℂ] ℂ) :
    Function.Surjective (Infinitesimal.tangentMap f p) := by
  have hf : f.toRingHom.Smooth :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)
      (φ := CommRingCat.ofHom f.toRingHom)).mp
        (show AlgebraicGeometry.Smooth (DirectionCones.affineMap f) from inferInstance)
  exact tangentMap_surjective_of_smooth f hf p

/-- A smooth affine source restriction gives surjectivity for the original
morphism at the image of its actual point. Only the composite is assumed
smooth: no product-open neighborhood or open-immersion premise is needed. -/
theorem tangentMap_surjective_of_smooth_restriction
    {D : Type} [CommRing D] [Algebra ℂ D]
    (f : A →ₐ[ℂ] B) (ρ : B →ₐ[ℂ] D) (q : D →ₐ[ℂ] ℂ)
    [AlgebraicGeometry.Smooth (DirectionCones.affineMap (ρ.comp f))] :
    Function.Surjective (Infinitesimal.tangentMap f (q.comp ρ)) := by
  intro v
  obtain ⟨E, hE⟩ := tangentMap_surjective_of_scheme_smooth (ρ.comp f) q v
  refine ⟨Infinitesimal.tangentMap ρ q E, ?_⟩
  calc
    Infinitesimal.tangentMap f (q.comp ρ) (Infinitesimal.tangentMap ρ q E) =
        Infinitesimal.tangentMap (ρ.comp f) q E := by
      apply Subtype.ext
      apply LinearMap.ext
      intro a
      rfl
    _ = v := hE

end SchemeSmoothness

end LeBrunSalamon.Construction.Lines.SmoothTangent

end

/-!
## Suitable pairs from smoothness of the actual velocity-sum morphism

This is the existing suitable-pair constructor with its actual differential
surjectivity supplied by formal smoothness. The morphism in the smoothness
hypothesis is precisely the sum formed from the two supplied actual velocity
factors. The actual free lines, their fixed centers, the factor identities,
and Levi nonorthogonality remain explicit geometric inputs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open scoped TensorProduct

namespace LeBrunSalamon.Construction.Lines.ActualVelocitySuitablePair

open IntrinsicVelocityRange ContactVelocityFactorization

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x)
variable (A B : Charts.PointedAffine)
variable (gA : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
variable (gB : PointsOver B.scheme B.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
variable (f₁ f₂ : FreeLine X)
variable (h₁ : marking.map ≫ f₁.curve.map = x.map)
variable (h₂ : marking.map ≫ f₂.curve.map = x.map)
variable (hat₁ : A.point.val ≫ gA.val =
  (HomDeformation.fixedCenter P H marking x f₁.curve.map f₁.curve.overC h₁).val)
variable (hat₂ : B.point.val ≫ gB.val =
  (HomDeformation.fixedCenter P H marking x f₂.curve.map f₂.curve.overC h₂).val)
variable (ψ₁ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] A.Ring)
variable (ψ₂ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] B.Ring)
variable (hψ₁ : ψ₁.comp (LinearVelocityTarget.quotientMap C.evaluation
  (ContactVelocityTarget.image X x C)) = velocityFunctions H x C A gA)
variable (hψ₂ : ψ₂.comp (LinearVelocityTarget.quotientMap C.evaluation
  (ContactVelocityTarget.image X x C)) = velocityFunctions H x C B gB)

/-- Smoothness of the actual product-parameter velocity sum supplies the
surjectivity premise of the original suitable-pair construction. This theorem
does not assert that the given sum morphism is smooth. -/
def from_smooth_actual_sum
    (htrans : NonzeroLeviPair X x
      (nodeDifferential f₁ x h₁ (SourceTangent.sourceVector marking))
      (nodeDifferential f₂ x h₂ (SourceTangent.sourceVector marking)))
    (hsmooth : Smooth (DirectionCones.affineMap
      (LinearVelocityAddition.parameterSum C.evaluation
        (ContactVelocityTarget.image X x C) ψ₁ ψ₂))) : SuitablePair X := by
  letI : Smooth (DirectionCones.affineMap
      (LinearVelocityAddition.parameterSum C.evaluation
        (ContactVelocityTarget.image X x C) ψ₁ ψ₂)) := hsmooth
  exact from_actual_sum_differential H x C A B gA gB f₁ f₂ h₁ h₂ hat₁ hat₂
    ψ₁ ψ₂ hψ₁ hψ₂ htrans
    (SmoothTangent.tangentMap_surjective_of_scheme_smooth
      (LinearVelocityAddition.parameterSum C.evaluation
        (ContactVelocityTarget.image X x C) ψ₁ ψ₂)
      (LinearVelocityAddition.tensorPoint A.evaluation B.evaluation))

/-- An affine neighborhood inside a smooth source open may be used without
requiring a product-open rectangle. Its actual point must map to the stated
tensor-product parameter point. The source map itself need not be an open
immersion for this differential-surjectivity inference. -/
def from_smooth_restricted_actual_sum
    {D : Type} [CommRing D] [Algebra ℂ D]
    (ρ : A.Ring ⊗[ℂ] B.Ring →ₐ[ℂ] D) (q : D →ₐ[ℂ] ℂ)
    (hcenter : q.comp ρ =
      LinearVelocityAddition.tensorPoint A.evaluation B.evaluation)
    (htrans : NonzeroLeviPair X x
      (nodeDifferential f₁ x h₁ (SourceTangent.sourceVector marking))
      (nodeDifferential f₂ x h₂ (SourceTangent.sourceVector marking)))
    (hsmooth : Smooth (DirectionCones.affineMap
      (ρ.comp (LinearVelocityAddition.parameterSum C.evaluation
        (ContactVelocityTarget.image X x C) ψ₁ ψ₂)))) : SuitablePair X := by
  letI : Smooth (DirectionCones.affineMap
      (ρ.comp (LinearVelocityAddition.parameterSum C.evaluation
        (ContactVelocityTarget.image X x C) ψ₁ ψ₂))) := hsmooth
  have hsurj : Function.Surjective (Infinitesimal.tangentMap
      (LinearVelocityAddition.parameterSum C.evaluation
        (ContactVelocityTarget.image X x C) ψ₁ ψ₂)
      (LinearVelocityAddition.tensorPoint A.evaluation B.evaluation)) := by
    exact Eq.mp (congrArg (fun s : A.Ring ⊗[ℂ] B.Ring →ₐ[ℂ] ℂ =>
      Function.Surjective (Infinitesimal.tangentMap
        (LinearVelocityAddition.parameterSum C.evaluation
          (ContactVelocityTarget.image X x C) ψ₁ ψ₂) s)) hcenter)
      (SmoothTangent.tangentMap_surjective_of_smooth_restriction
        (LinearVelocityAddition.parameterSum C.evaluation
          (ContactVelocityTarget.image X x C) ψ₁ ψ₂) ρ q)
  exact from_actual_sum_differential H x C A B gA gB f₁ f₂ h₁ h₂ hat₁ hat₂
    ψ₁ ψ₂ hψ₁ hψ₂ htrans hsurj

end LeBrunSalamon.Construction.Lines.ActualVelocitySuitablePair

end

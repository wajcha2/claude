import LSHomVelocity

/-!
## Actual affine tangent lifts, with normalized maps on functions

The parameter directions used in the velocity argument are point derivations
on an actual affine chart. They are sent to actual dual-number scheme maps
through the canonical affine isomorphism with the spectrum of global sections.
The construction and its naturality do not use the historical admitted
`Charts.PointedAffine.tangentLiftEquiv_exists`.

This is new source; check it at the 45,000-line project gate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Charts.AffineTangentLift

/-- Functions on the inverse of the canonical affine chart isomorphism. -/
theorem isoSpec_inv_appTop (Y : Scheme) [IsAffine Y] :
    Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso (Y.presheaf.obj (op ⊤))).inv := by
  apply (cancel_mono (Scheme.ΓSpecIso (Y.presheaf.obj (op ⊤))).hom).mp
  rw [← Scheme.toSpecΓ_appTop]
  rw [← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv]
  simp

/-- Realize a homomorphism from the actual global sections of an affine
scheme as an actual map from a spectrum. -/
def fromFunctions (Y : Scheme) [IsAffine Y] {R : Type} [CommRing R]
    (φ : RingSections Y ⊤ →+* R) : Spec (CommRingCat.of R) ⟶ Y :=
  Spec.map (CommRingCat.ofHom φ) ≫ Y.isoSpec.inv

theorem fromFunctions_appTop (Y : Scheme) [IsAffine Y]
    {R : Type} [CommRing R] (φ : RingSections Y ⊤ →+* R) :
    (fromFunctions Y φ).appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
  rw [fromFunctions, Scheme.Hom.comp_appTop, isoSpec_inv_appTop]
  exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm

theorem fromFunctions_apply (Y : Scheme) [IsAffine Y]
    {R : Type} [CommRing R] (φ : RingSections Y ⊤ →+* R)
    (a : RingSections Y ⊤) :
    (fromFunctions Y φ).appTop a =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv (φ a) := by
  rw [fromFunctions_appTop]
  rfl

theorem fromFunctions_unique (Y : Scheme) [IsAffine Y]
    {R : Type} [CommRing R] (φ : RingSections Y ⊤ →+* R)
    (g : Spec (CommRingCat.of R) ⟶ Y)
    (hg : ∀ a, g.appTop a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv (φ a)) :
    g = fromFunctions Y φ := by
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  rw [fromFunctions_apply]
  exact hg a

section Pointed

variable (A : PointedAffine)

/-- Every algebra map to the actual dual-number ring gives an over-C map
to the affine chart. Reduction is an additional condition, proved below. -/
theorem fromFunctions_overC (φ : A.Ring →ₐ[ℂ] Infinitesimal.Dual) :
    fromFunctions A.scheme φ.toRingHom ≫ A.toC = Infinitesimal.dualToC := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change (fromFunctions A.scheme φ.toRingHom).appTop
      (A.toC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) =
    Infinitesimal.dualToC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  rw [← complexConstants_apply_top, fromFunctions_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
      (φ (algebraMap ℂ A.Ring c)) = _
  rw [φ.commutes]
  exact congrArg (fun k : CommRingCat.of ℂ ⟶
      (Spec (CommRingCat.of Infinitesimal.Dual)).presheaf.obj (op ⊤) => k c)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)))

/-- The residue condition is exactly the reduction equation of scheme maps. -/
theorem fromFunctions_reduces (φ : A.Ring →ₐ[ℂ] Infinitesimal.Dual)
    (hφ : Infinitesimal.residue.comp φ = A.evaluation) :
    Infinitesimal.origin ≫ fromFunctions A.scheme φ.toRingHom = A.point.val := by
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change Infinitesimal.origin.appTop
    ((fromFunctions A.scheme φ.toRingHom).appTop a) = A.point.val.appTop a
  rw [fromFunctions_apply]
  have hnat := congrArg (fun k : CommRingCat.of Infinitesimal.Dual ⟶
      (Spec (CommRingCat.of ℂ)).presheaf.obj (op ⊤) => k (φ a))
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom Infinitesimal.residue.toRingHom))
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
      (Infinitesimal.residue (φ a)) =
    Infinitesimal.origin.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv (φ a)) at hnat
  change Infinitesimal.origin.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv (φ a)) = _
  have hres : Infinitesimal.residue (φ a) = A.evaluation a :=
    congrArg (fun k : A.Ring →ₐ[ℂ] ℂ => k a) hφ
  exact hnat.symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv hres).trans
    (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) (A.point.val.appTop a)))

/-- The actual tangent lift, constructed without the old existence admission. -/
def lift (D : A.Tangent) : Infinitesimal.PointLift A.scheme A.toC A.point where
  map := fromFunctions A.scheme (Infinitesimal.tangentToDual A.evaluation D).toRingHom
  overC := fromFunctions_overC A (Infinitesimal.tangentToDual A.evaluation D)
  reduces := fromFunctions_reduces A (Infinitesimal.tangentToDual A.evaluation D)
    (Infinitesimal.tangentToDual_residue A.evaluation D)

theorem lift_normalized (D : A.Tangent) (a : A.Ring) :
    (lift A D).map.appTop a =
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        (Infinitesimal.tangentToDual A.evaluation D a) :=
  fromFunctions_apply A.scheme (Infinitesimal.tangentToDual A.evaluation D).toRingHom a

theorem lift_linearCoefficient (D : A.Tangent) (a : A.Ring) :
    Infinitesimal.linearCoefficient
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
        ((lift A D).map.appTop a)) = D.val a := by
  rw [lift_normalized]
  simp only [Iso.inv_hom_id_apply]
  exact Infinitesimal.linearCoefficient_normalForm _ _

/-- The normalized action on functions recovers the derivation, so the
constructed point lifts do not identify different parameter directions. -/
theorem lift_injective : Function.Injective (lift A) := by
  intro D E h
  apply Subtype.ext
  ext a
  have he := congrArg (fun v : Infinitesimal.PointLift A.scheme A.toC A.point =>
    Infinitesimal.linearCoefficient
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom (v.map.appTop a))) h
  exact (lift_linearCoefficient A D a).symm.trans (he.trans (lift_linearCoefficient A E a))

/-- The algebra map of an actual chart lift, normalized by Γ(Spec Dual). -/
def functionsOfLift (v : Infinitesimal.PointLift A.scheme A.toC A.point) :
    A.Ring →ₐ[ℂ] Infinitesimal.Dual where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom.hom.comp
    v.map.appTop.hom
  commutes' := by
    intro c
    change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
        (v.map.appTop (complexConstants A.toC c)) = algebraMap ℂ Infinitesimal.Dual c
    rw [complexConstants_naturality v.map Infinitesimal.dualToC A.toC v.overC,
      complexConstants_apply_top]
    have hnat := congrArg (fun k : CommRingCat.of ℂ ⟶
        (Spec (CommRingCat.of Infinitesimal.Dual)).presheaf.obj (op ⊤) => k c)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)))
    change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        (algebraMap ℂ Infinitesimal.Dual c) =
      Infinitesimal.dualToC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) at hnat
    rw [← hnat]
    simp

theorem functionsOfLift_residue
    (v : Infinitesimal.PointLift A.scheme A.toC A.point) :
    Infinitesimal.residue.comp (functionsOfLift A v) = A.evaluation := by
  ext a
  have hnat := congrArg (fun k :
      (Spec (CommRingCat.of Infinitesimal.Dual)).presheaf.obj (op ⊤) ⟶
        CommRingCat.of ℂ => k (v.map.appTop a))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom Infinitesimal.residue.toRingHom))
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (Infinitesimal.origin.appTop (v.map.appTop a)) =
    Infinitesimal.residue
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom (v.map.appTop a)) at hnat
  change Infinitesimal.residue
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom (v.map.appTop a)) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (A.point.val.appTop a)
  rw [← hnat]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((Infinitesimal.origin ≫ v.map).appTop a) = _
  rw [v.reduces]

theorem functionsOfLift_lift (D : A.Tangent) :
    functionsOfLift A (lift A D) = Infinitesimal.tangentToDual A.evaluation D := by
  ext a
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
    ((lift A D).map.appTop a) = _
  rw [lift_normalized]
  simp

theorem pointLift_ext {v w : Infinitesimal.PointLift A.scheme A.toC A.point}
    (h : v.map = w.map) : v = w := by
  cases v
  cases w
  cases h
  rfl

/-- Conversely, every actual infinitesimal chart point is the lift of its
point derivation. This is proved from the explicit dual-number bijection. -/
theorem lift_surjective : Function.Surjective (lift A) := by
  intro v
  let φ : {q : A.Ring →ₐ[ℂ] Infinitesimal.Dual //
      Infinitesimal.residue.comp q = A.evaluation} :=
    ⟨functionsOfLift A v, functionsOfLift_residue A v⟩
  obtain ⟨D, hD⟩ := (Infinitesimal.tangentToDual_bijective A.evaluation).2 φ
  refine ⟨D, pointLift_ext A ?_⟩
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  rw [lift_normalized]
  have he : Infinitesimal.tangentToDual A.evaluation D a = functionsOfLift A v a :=
    congrArg (fun q : {q : A.Ring →ₐ[ℂ] Infinitesimal.Dual //
      Infinitesimal.residue.comp q = A.evaluation} => q.val a) hD
  rw [he]
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
    ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom (v.map.appTop a)) = _
  simp

/-- This explicit construction can eventually replace the historical admitted
affine equivalence. Its forward map is the explicit Spec map above. -/
def equivalence : A.Tangent ≃ Infinitesimal.PointLift A.scheme A.toC A.point :=
  Equiv.ofBijective (lift A) ⟨lift_injective A, lift_surjective A⟩

end Pointed

section Naturality

/-- Push an actual point lift along an actual morphism over C. No affineness
of the target parameter scheme is needed. -/
def push {S T : Scheme} {sS : S ⟶ ComplexBase} {sT : T ⟶ ComplexBase}
    {s : PointsOver ComplexBase (𝟙 ComplexBase) S sS}
    {t : PointsOver ComplexBase (𝟙 ComplexBase) T sT}
    (g : S ⟶ T) (hg : g ≫ sT = sS) (hat : s.val ≫ g = t.val)
    (v : Infinitesimal.PointLift S sS s) : Infinitesimal.PointLift T sT t where
  map := v.map ≫ g
  overC := by rw [Category.assoc, hg, v.overC]
  reduces := by rw [← Category.assoc, v.reduces, hat]

/-- Naturality is equality of actual maps on the dual-number test scheme. -/
theorem lift_natural {A B : PointedAffine} (f : Charts.Hom A B) (D : A.Tangent) :
    (lift A D).map ≫ f.map = (lift B (f.differential D)).map := by
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (lift A D).map.appTop (f.map.appTop a) = _
  rw [lift_normalized, lift_normalized]
  apply congrArg (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
  change algebraMap ℂ Infinitesimal.Dual (A.evaluation (f.onFunctions a)) +
      Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (D.val (f.onFunctions a)) =
    algebraMap ℂ Infinitesimal.Dual (B.evaluation a) +
      Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual ((f.differential D).val a)
  rw [Charts.Hom.evaluation_onFunctions, Charts.Hom.differential_apply]

/-- The zero vector is exactly the constant point lift. The reduction
proof uses the proved Spec functoriality equation, not the old admission. -/
def zeroLift (A : PointedAffine) :
    Infinitesimal.PointLift A.scheme A.toC A.point where
  map := Infinitesimal.dualToC ≫ A.point.val
  overC := by rw [Category.assoc, A.point.property, Category.comp_id]
  reduces := by rw [← Category.assoc, Lines.DualThickening.origin_overC, Category.id_comp]

theorem lift_zero (A : PointedAffine) : lift A 0 = zeroLift A := by
  apply pointLift_ext A
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  rw [lift_normalized]
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
      (algebraMap ℂ Infinitesimal.Dual (A.evaluation a) +
        Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (0 : ℂ)) =
    Infinitesimal.dualToC.appTop (A.point.val.appTop a)
  simp only [map_zero, mul_zero, add_zero]
  have hnat := congrArg (fun k :
      (Spec (CommRingCat.of ℂ)).presheaf.obj (op ⊤) ⟶
        CommRingCat.of Infinitesimal.Dual => k (A.point.val.appTop a))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)))
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
      (Infinitesimal.dualToC.appTop (A.point.val.appTop a)) =
    algebraMap ℂ Infinitesimal.Dual (A.evaluation a) at hnat
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom).1
  simpa only [Iso.inv_hom_id_apply] using hnat.symm

/-- Vanishing of the ordinary chart differential is equivalent to the
actual infinitesimal image being constant. -/
theorem differential_zero_iff {A B : PointedAffine}
    (f : Charts.Hom A B) (D : A.Tangent) :
    f.differential D = 0 ↔
      (lift A D).map ≫ f.map = Infinitesimal.dualToC ≫ B.point.val := by
  rw [lift_natural]
  constructor
  · intro h
    rw [h, lift_zero]
    rfl
  · intro h
    apply lift_injective B
    rw [lift_zero]
    exact pointLift_ext B h

end Naturality

end LeBrunSalamon.Construction.Charts.AffineTangentLift

end

/-!
## A nonconstant source lift at the actual marking

The existing marking is not identified with the origin of a chosen polynomial
chart. We instead use an actual standard chart containing it, keep its actual
coordinate c, and differentiate at c. The resulting source lift is proved
nonconstant as a map from Spec(C[epsilon]/epsilon²).

Comparison with the original source tangent-sheaf fiber is a further step;
nonconstancy alone is not used as an arbitrary tangent-fiber identification.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.P1Charts

namespace LeBrunSalamon.Construction.Lines.PolynomialSourceLift

/-- Differentiation in the actual polynomial coordinate at c. -/
def derivation (c : ℂ) :
    Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c) :=
  ⟨(Polynomial.aeval c).toLinearMap.comp Polynomial.derivative, by
    intro a b
    change Polynomial.aeval c (Polynomial.derivative (a*b)) =
      Polynomial.aeval c a * Polynomial.aeval c (Polynomial.derivative b) +
        Polynomial.aeval c b * Polynomial.aeval c (Polynomial.derivative a)
    rw [Polynomial.derivative_mul, map_add, map_mul, map_mul]
    ring⟩

@[simp] theorem derivation_apply (c : ℂ) (a : Polynomial ℂ) :
    (derivation c).val a = Polynomial.aeval c (Polynomial.derivative a) := rfl

@[simp] theorem derivation_X (c : ℂ) : (derivation c).val Polynomial.X = 1 := by
  simp [derivation_apply]

theorem derivation_ne_zero (c : ℂ) : derivation c ≠ 0 := by
  intro h
  have hx := congrArg (fun D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c) =>
    D.val Polynomial.X) h
  simpa using hx

/-- The actual polynomial coordinate of the source first jet is c+epsilon. -/
theorem tangentToDual_X (c : ℂ) :
    Infinitesimal.tangentToDual (Polynomial.aeval c) (derivation c) Polynomial.X =
      algebraMap ℂ Infinitesimal.Dual c + Infinitesimal.epsilon := by
  change algebraMap ℂ Infinitesimal.Dual (Polynomial.aeval c Polynomial.X) +
    Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
      ((derivation c).val Polynomial.X) = _
  rw [Polynomial.aeval_X, derivation_X, map_one, mul_one]

/-- An actual lift into a standard polynomial chart, then its open immersion
into the original projective line. -/
def mapAt (i : Fin 2) (c : ℂ) : Infinitesimal.DualScheme ⟶ ProjectiveLine :=
  Spec.map (CommRingCat.ofHom
    (Infinitesimal.tangentToDual (Polynomial.aeval c) (derivation c)).toRingHom) ≫
      polynomialChartInclusion i

theorem mapAt_overC (i : Fin 2) (c : ℂ) :
    mapAt i c ≫ canonicalProjectiveLine.structureMap = Infinitesimal.dualToC := by
  change (Spec.map (CommRingCat.ofHom
      (Infinitesimal.tangentToDual (Polynomial.aeval c) (derivation c)).toRingHom) ≫
    polynomialChartInclusion i) ≫ canonicalBaseMap = _
  rw [Category.assoc, polynomialChartInclusion_baseMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (Infinitesimal.tangentToDual (Polynomial.aeval c) (derivation c)).commutes a

theorem mapAt_reduces (i : Fin 2) (c : ℂ) :
    Infinitesimal.origin ≫ mapAt i c = pointMap i c := by
  rw [mapAt, Infinitesimal.origin, ← Category.assoc, ← Spec.map_comp,
    pointMap_eq_polynomialChart]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact congrArg (fun q : Polynomial ℂ →ₐ[ℂ] ℂ => q a)
    (Infinitesimal.tangentToDual_residue (Polynomial.aeval c) (derivation c))

/-- At each concrete chart point, the normalized source lift is an actual
over-C infinitesimal point with the specified central morphism. -/
def liftAt (i : Fin 2) (c : ℂ) :
    HomFirstJet.SourceLift canonicalProjectiveLine
      (⟨pointMap i c, pointMap_overC i c⟩ : ProjectiveLinePoint canonicalProjectiveLine) where
  map := mapAt i c
  overC := mapAt_overC i c
  reduces := mapAt_reduces i c

/-- The chosen source first jet is not the constant infinitesimal point.
The proof detects the epsilon coefficient in the genuine polynomial chart. -/
theorem mapAt_nonconstant (i : Fin 2) (c : ℂ) :
    mapAt i c ≠ Infinitesimal.dualToC ≫ pointMap i c := by
  intro h
  rw [mapAt, pointMap_eq_polynomialChart, ← Category.assoc] at h
  have hc := (cancel_mono (polynomialChartInclusion i)).mp h
  rw [Infinitesimal.dualToC, ← Spec.map_comp] at hc
  have hr := Spec.map_injective hc
  have hx := congrArg (fun q : CommRingCat.of (Polynomial ℂ) ⟶
    CommRingCat.of Infinitesimal.Dual => q Polynomial.X) hr
  change Infinitesimal.tangentToDual (Polynomial.aeval c) (derivation c) Polynomial.X =
    algebraMap ℂ Infinitesimal.Dual (Polynomial.eval c Polynomial.X) at hx
  rw [tangentToDual_X, Polynomial.eval_X] at hx
  exact Infinitesimal.epsilon_ne_zero (add_left_cancel (hx.trans (add_zero _).symm))

/-- A coordinate chart for the actual marking. Its coordinate is retained;
the abstract projective-coordinate presentation does not set it to zero. -/
structure MarkingChart (p : ProjectiveLinePoint canonicalProjectiveLine) where
  index : Fin 2
  coordinate : ℂ
  identifies : pointMap index coordinate = p.map

theorem markingChart_nonempty (p : ProjectiveLinePoint canonicalProjectiveLine) :
    Nonempty (MarkingChart p) := by
  obtain ⟨i, c, h⟩ := canonicalPoint_is_coordinate p.map p.overC
  exact ⟨⟨i, c, h⟩⟩

def markingChart (p : ProjectiveLinePoint canonicalProjectiveLine) : MarkingChart p :=
  Classical.choice (markingChart_nonempty p)

/-- The source lift used by the velocity construction at the original point. -/
def atMarking (p : ProjectiveLinePoint canonicalProjectiveLine) :
    HomFirstJet.SourceLift canonicalProjectiveLine p where
  map := mapAt (markingChart p).index (markingChart p).coordinate
  overC := mapAt_overC _ _
  reduces := (mapAt_reduces _ _).trans (markingChart p).identifies

theorem atMarking_nonconstant (p : ProjectiveLinePoint canonicalProjectiveLine) :
    (atMarking p).map ≠ Infinitesimal.dualToC ≫ p.map := by
  intro h
  apply mapAt_nonconstant (markingChart p).index (markingChart p).coordinate
  exact h.trans (congrArg (fun k : ComplexBase ⟶ ProjectiveLine =>
    Infinitesimal.dualToC ≫ k) (markingChart p).identifies.symm)

end LeBrunSalamon.Construction.Lines.PolynomialSourceLift

end

/-!
## The two actual infinitesimal restrictions of the universal family

The parameter direction and the source direction are independent copies of
Spec(C[epsilon]/epsilon²). Interchanging the pullback projections identifies
the two restrictions of the actual universal map. This is an equality of
scheme maps on the full double thickening, including its nonzero mixed term.
No asserted equality of differentials is supplied as a hypothesis.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.MixedFamily

abbrev DoubleDual : Scheme := DualThickening.space Infinitesimal.dualToC

/-- Swap the two genuine dual-number factors of their scheme pullback. -/
def swap : DoubleDual ⟶ DoubleDual :=
  pullback.lift (DualThickening.parameter Infinitesimal.dualToC)
    (DualThickening.projection Infinitesimal.dualToC) pullback.condition.symm

@[simp] theorem swap_projection :
    swap ≫ DualThickening.projection Infinitesimal.dualToC =
      DualThickening.parameter Infinitesimal.dualToC := by
  simp [swap, DualThickening.projection]

@[simp] theorem swap_parameter :
    swap ≫ DualThickening.parameter Infinitesimal.dualToC =
      DualThickening.projection Infinitesimal.dualToC := by
  simp [swap, DualThickening.parameter]

theorem swap_overC : swap ≫ DualThickening.toC Infinitesimal.dualToC =
    DualThickening.toC Infinitesimal.dualToC := by
  rw [DualThickening.toC, ← Category.assoc, swap_projection]
  exact DualThickening.parameter_overC Infinitesimal.dualToC

theorem swap_involutive : swap ≫ swap = 𝟙 DoubleDual := by
  apply pullback.hom_ext
  · change (swap ≫ swap) ≫ DualThickening.projection Infinitesimal.dualToC = _
    rw [Category.assoc, swap_projection, swap_parameter, Category.id_comp]
    rfl
  · change (swap ≫ swap) ≫ DualThickening.parameter Infinitesimal.dualToC = _
    rw [Category.assoc, swap_parameter, swap_projection, Category.id_comp]
    rfl

def swapIso : DoubleDual ≅ DoubleDual where
  hom := swap
  inv := swap
  hom_inv_id := swap_involutive
  inv_hom_id := swap_involutive

/-- A first-order parameter change and a first-order source restriction
define the same map to the actual source product after swapping the factors. -/
theorem source_parameter_interchange
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (τ : HomFirstJet.SourceLift P p)
    (v : PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC T sT) :
    HomFirstJet.sourceMap P p Infinitesimal.dualToC τ ≫ rationalSourceMap P v =
      swap ≫ DualThickening.map τ.map τ.overC ≫ rationalSourceMap P v := by
  apply pullback.hom_ext
  · change _ ≫ pullback.fst P.structureMap sT = _
    simp only [Category.assoc, rationalSourceMap, pullback.lift_fst,
      HomFirstJet.sourceMap_fst]
    change DualThickening.parameter Infinitesimal.dualToC ≫ τ.map =
      swap ≫ (DualThickening.map τ.map τ.overC ≫ DualThickening.projection P.structureMap)
    rw [DualThickening.map_projection, ← Category.assoc, swap_projection]
  · change _ ≫ pullback.snd P.structureMap sT = _
    simp only [Category.assoc, rationalSourceMap, pullback.lift_snd]
    rw [← Category.assoc, HomFirstJet.sourceMap_snd]
    change DualThickening.projection Infinitesimal.dualToC ≫ v.val =
      swap ≫ (DualThickening.map τ.map τ.overC ≫
        DualThickening.parameter P.structureMap) ≫ v.val
    rw [DualThickening.map_parameter, ← Category.assoc, swap_parameter]

section ActualHom

variable (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X) (x : ComplexPoint X)
variable (τ : HomFirstJet.SourceLift P p)
variable (t : PointsOver ComplexBase (𝟙 ComplexBase)
  (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x))
variable (v : Infinitesimal.PointLift (FixedNodeHom.parameter P p H x)
  (FixedNodeHom.toC P p H x) t)

/-- First take the source first jet of the global family, then the actual
parameter tangent. -/
def sourceThenParameter : DoubleDual ⟶ X.scheme :=
  ((HomFirstJet.deformation P p H x τ).pullback v.map v.overC).map

/-- First take the actual parameter deformation, then the source first jet.
Its source is the same pullback with the two factor labels reversed. -/
def parameterThenSource : DoubleDual ⟶ X.scheme :=
  ((HomDeformation.deformation P p H x t v).pullback τ.map τ.overC).map

theorem sourceThenParameter_overC :
    sourceThenParameter P p H x τ t v ≫ X.structureMap =
      DualThickening.toC Infinitesimal.dualToC :=
  ((HomFirstJet.deformation P p H x τ).pullback v.map v.overC).overC

theorem parameterThenSource_overC :
    parameterThenSource P p H x τ t v ≫ X.structureMap =
      DualThickening.toC Infinitesimal.dualToC :=
  ((HomDeformation.deformation P p H x t v).pullback τ.map τ.overC).overC

/-- Equality of the actual two-variable restrictions of the original Hom
evaluation map. In particular, the mixed coefficient belongs to one family. -/
theorem restrictions_interchange :
    sourceThenParameter P p H x τ t v =
      swap ≫ parameterThenSource P p H x τ t v := by
  unfold sourceThenParameter
  rw [HomFirstJet.deformation_parameterChange P p H x τ
    (⟨v.map, v.overC⟩ : PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x))]
  change HomFirstJet.sourceMap P p Infinitesimal.dualToC τ ≫
      rationalSourceMap P (⟨v.map, v.overC⟩ :
        PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC
          (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) ≫
      FixedNodeHom.evaluation P p H x = _
  rw [← Category.assoc, source_parameter_interchange]
  simp only [parameterThenSource, FamilyVariation.Deformation.pullback,
    HomDeformation.deformation, Category.assoc]

/-- The equality survives target chart pullbacks on global functions. -/
theorem restrictions_appTop (a : RingSections X.scheme ⊤) :
    (sourceThenParameter P p H x τ t v).appTop a =
      swap.appTop ((parameterThenSource P p H x τ t v).appTop a) := by
  rw [restrictions_interchange, Scheme.Hom.comp_appTop]
  rfl

/-- If a target function is local, use the genuine common inverse-image
open under the two equal scheme maps. This statement imposes no product-open
assumption and can be applied after factoring through a target chart. -/
theorem restrictions_appLE (U : X.scheme.Opens) (W : DoubleDual.Opens)
    (hW : W ≤ sourceThenParameter P p H x τ t v ⁻¹ᵁ U) :
    (sourceThenParameter P p H x τ t v).appLE U W hW =
      (swap ≫ parameterThenSource P p H x τ t v).appLE U W
        (by simpa only [← restrictions_interchange] using hW) :=
  DualThickening.appLE_of_map_eq (restrictions_interchange P p H x τ t v) U W _ _

/-- The source-first reduction is the constant target node, over the entire
remaining parameter dual-number scheme. -/
theorem sourceThenParameter_source_zero :
    DualThickening.zeroSection Infinitesimal.dualToC ≫
      sourceThenParameter P p H x τ t v = Infinitesimal.dualToC ≫ x.map := by
  change DualThickening.zeroSection Infinitesimal.dualToC ≫
      ((HomFirstJet.deformation P p H x τ).pullback v.map v.overC).map = _
  rw [((HomFirstJet.deformation P p H x τ).pullback v.map v.overC).reduces]
  rw [← Category.assoc, v.overC]

/-- The parameter-first reduction is the source first jet of the original
central curve, retaining its actual source derivative. -/
theorem parameterThenSource_parameter_zero :
    DualThickening.zeroSection Infinitesimal.dualToC ≫
      parameterThenSource P p H x τ t v = τ.map ≫ HomDeformation.curveAt P H p x t :=
  ((HomDeformation.deformation P p H x t v).pullback τ.map τ.overC).reduces

end ActualHom

end LeBrunSalamon.Construction.Lines.MixedFamily

end

/-!
## Actual functions on a dual thickening and the tensor-product first jet

The section algebra remembers its specified complex structure morphism.
The comparison below is fixed by the actual projection and the actual
epsilon. Its two coefficients are exactly the previously constructed
scheme-theoretic reduction and infinitesimal coefficient on every open.

This constructs the missing algebra comparison, rather than positing an
identification of an abstract first-jet ring with the functions of a family.
Naturality is proved for actual source changes, and the mixed coefficient
of a pulled-back family is the derivative of its actual regular coefficient.

Unchecked continuation; the next compiler gate is 45,000 project lines.
No additional standard input or manuscript-specific admission is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.SectionAlgebra

/-- Actual functions, with the specified complex structure retained in the
type so that scalar structures from different base maps are never conflated. -/
def Functions {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) : Type _ :=
  RingSections Y U

instance functionsCommRing {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    CommRing (Functions sY U) := inferInstanceAs (CommRing (RingSections Y U))

instance functionsAlgebra {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    Algebra ℂ (Functions sY U) := (ScalarSections.constantsOn sY U).toAlgebra

theorem algebraMap_apply {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (c : ℂ) :
    algebraMap ℂ (Functions sY U) c = complexConstant sY U c := rfl

theorem algebraMap_top {Y : Scheme} (sY : Y ⟶ ComplexBase) (c : ℂ) :
    algebraMap ℂ (Functions sY ⊤) c = complexConstants sY c := rfl

/-- Pullback of constants on arbitrary opens follows from the original
sheaf naturality square and the actual equation over the complex base. -/
theorem constants_naturality {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens) (c : ℂ) :
    g.app U (complexConstant sZ U c) =
      complexConstant sY (g ⁻¹ᵁ U) c := by
  have hn := congrArg (fun k => k
    (sZ.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)))
    (g.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change g.app U (complexConstant sZ U c) =
    Y.presheaf.map (homOfLE le_top).op
      (g.appTop (sZ.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) at hn
  have hc := complexConstants_naturality g sY sZ hg c
  rw [complexConstants_apply_top, complexConstants_apply_top] at hc
  rw [hc] at hn
  exact hn

/-- Restriction keeps the given complex algebra structure. -/
def restrict {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {U V : Y.Opens} (i : U ⟶ V) : Functions sY V →ₐ[ℂ] Functions sY U where
  toRingHom := (Y.presheaf.map i.op).hom
  commutes' c := ScalarSections.complexConstant_restrict sY i c

/-- The actual pullback of functions is a complex algebra homomorphism. -/
def onFunctions {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens) :
    Functions sZ U →ₐ[ℂ] Functions sY (g ⁻¹ᵁ U) where
  toRingHom := (g.app U).hom
  commutes' := constants_naturality g hg U

/-- Pullback followed by the actual open restriction; the inequality is
only the domain on which this function is defined. -/
def onFunctionsLE {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens)
    (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U) :
    Functions sZ U →ₐ[ℂ] Functions sY V :=
  (restrict sY (homOfLE hV)).comp (onFunctions g hg U)

theorem onFunctionsLE_apply {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens)
    (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U) (a : Functions sZ U) :
    onFunctionsLE g hg U V hV a = g.appLE U V hV a := rfl

def onFunctionsTop {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) :
    Functions sZ ⊤ →ₐ[ℂ] Functions sY ⊤ := onFunctions g hg ⊤

theorem onFunctionsTop_apply {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (a : Functions sZ ⊤) :
    onFunctionsTop g hg a = g.appTop a := rfl

theorem restrict_comp {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {U V W : Y.Opens} (i : U ⟶ V) (j : V ⟶ W) :
    (restrict sY i).comp (restrict sY j) = restrict sY (i ≫ j) := by
  ext a
  change (Y.presheaf.map j.op ≫ Y.presheaf.map i.op) a =
    Y.presheaf.map (i ≫ j).op a
  rw [← Functor.map_comp]
  rfl

theorem onFunctions_comp {Y Z W : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase} {sW : W ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY)
    (h : Z ⟶ W) (hh : h ≫ sW = sZ) (U : W.Opens) :
    (onFunctions g hg (h ⁻¹ᵁ U)).comp (onFunctions h hh U) =
      onFunctions (g ≫ h) (by rw [Category.assoc, hh, hg]) U := by
  ext a
  change (h.app U ≫ g.app (h ⁻¹ᵁ U)) a = (g ≫ h).app U a
  rw [Scheme.Hom.comp_app]
  rfl

end LeBrunSalamon.Construction.Lines.SectionAlgebra

namespace LeBrunSalamon.Construction.Lines.DualThickening

open SectionAlgebra

/-- The actual functions on the full inverse-image open of the thickening. -/
abbrev ThickenedFunctions {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :=
  Functions (toC sY) (projection sY ⁻¹ᵁ U)

def projectionFunctions {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    Functions sY U →ₐ[ℂ] ThickenedFunctions sY U :=
  onFunctions (projection sY) rfl U

theorem thickened_algebraMap {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (c : ℂ) :
    algebraMap ℂ (ThickenedFunctions sY U) c =
      (projection sY).app U (algebraMap ℂ (Functions sY U) c) :=
  (projectionFunctions sY U).commutes c |>.symm

@[simp] theorem coefficient_one {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) : coefficient sY U 1 = 0 := by
  simpa only [map_one] using coefficient_projection sY U 1

@[simp] theorem reductionCoefficient_one {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) : reductionCoefficient sY U 1 = 1 := by
  simpa only [map_one] using reductionCoefficient_projection sY U 1

@[simp] theorem coefficient_epsilon {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) : coefficient sY U (epsilonOn sY U) = 1 := by
  have h : normalForm sY U 0 1 = epsilonOn sY U := by simp [normalForm]
  rw [← h, coefficient_normalForm]

@[simp] theorem reductionCoefficient_epsilon {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    reductionCoefficient sY U (epsilonOn sY U) = 0 := by
  have h : normalForm sY U 0 1 = epsilonOn sY U := by simp [normalForm]
  rw [← h, reductionCoefficient_normalForm]

@[simp] theorem coefficient_algebraMap {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (c : ℂ) :
    coefficient sY U (algebraMap ℂ (ThickenedFunctions sY U) c) = 0 := by
  rw [thickened_algebraMap, coefficient_projection]

@[simp] theorem reductionCoefficient_algebraMap {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens) (c : ℂ) :
    reductionCoefficient sY U (algebraMap ℂ (ThickenedFunctions sY U) c) =
      algebraMap ℂ (Functions sY U) c := by
  rw [thickened_algebraMap, reductionCoefficient_projection]

theorem coefficient_smul {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (c : ℂ) (z : ThickenedFunctions sY U) :
    coefficient sY U (@SMul.smul ℂ (ThickenedFunctions sY U) inferInstance c z) =
      @SMul.smul ℂ (Functions sY U) inferInstance c (coefficient sY U z) := by
  let z₀ : RingSections (space sY) (projection sY ⁻¹ᵁ U) := z
  let c₀ : RingSections (space sY) (projection sY ⁻¹ᵁ U) :=
    algebraMap ℂ (ThickenedFunctions sY U) c
  let c₁ : RingSections Y U := algebraMap ℂ (Functions sY U) c
  change coefficient sY U (c₀ * z₀) = c₁ * coefficient sY U z₀
  have hc : c₀ = (projection sY).app U c₁ := thickened_algebraMap sY U c
  rw [hc, coefficient_mul, reductionCoefficient_projection,
    coefficient_projection, mul_zero, add_zero]

def coefficientLinear {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    ThickenedFunctions sY U →ₗ[ℂ] Functions sY U where
  toFun := coefficient sY U
  map_add' := coefficient_add sY U
  map_smul' := coefficient_smul sY U

def reductionFunctions {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    ThickenedFunctions sY U →ₐ[ℂ] Functions sY U where
  toFun := reductionCoefficient sY U
  map_zero' := reductionCoefficient_zero sY U
  map_one' := reductionCoefficient_one sY U
  map_add' := reductionCoefficient_add sY U
  map_mul' := reductionCoefficient_mul sY U
  commutes' := reductionCoefficient_algebraMap sY U

/-- This reduction map is the actual zero-section map on functions. -/
theorem reductionFunctions_apply {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (z : ThickenedFunctions sY U) :
    reductionFunctions sY U z = reductionHom sY U z :=
  reductionCoefficient_eq_reductionHom sY U z

/-- The canonical first-jet algebra comparison sends an actual function
to its actual two coefficients. No affine assumption on the source occurs. -/
def toTensor {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    ThickenedFunctions sY U →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] Functions sY U) where
  toFun z := (1 : MixedJet.Dual) ⊗ₜ[ℂ] reductionFunctions sY U z +
    Infinitesimal.epsilon ⊗ₜ[ℂ] coefficientLinear sY U z
  map_zero' := by simp
  map_one' := by
    have hc : coefficientLinear sY U 1 = 0 := coefficient_one sY U
    simp [hc, Algebra.TensorProduct.one_def]
  map_add' := by
    intro z w
    simp only [map_add, TensorProduct.tmul_add]
    abel
  map_mul' := by
    intro z w
    apply MixedJet.source_ext
    · simp only [map_mul, map_add, MixedJet.sourceZero_constant,
        MixedJet.sourceZero_linear, add_zero]
    · simp only [MixedJet.sourceDerivative_mul, map_add,
        MixedJet.sourceDerivative_constant, MixedJet.sourceDerivative_linear,
        MixedJet.sourceZero_constant, MixedJet.sourceZero_linear,
        zero_add, add_zero]
      exact coefficient_mul sY U z w
  commutes' := by
    intro c
    have hc : coefficientLinear sY U (algebraMap ℂ (ThickenedFunctions sY U) c) = 0 :=
      coefficient_algebraMap sY U c
    rw [AlgHom.commutes, hc,
      TensorProduct.tmul_zero, add_zero]
    exact (Algebra.TensorProduct.algebraMap_apply' c).symm

@[simp] theorem sourceZero_toTensor {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (z : ThickenedFunctions sY U) :
    MixedJet.sourceZero (toTensor sY U z) = reductionCoefficient sY U z := by
  simp [toTensor, reductionFunctions]

@[simp] theorem sourceDerivative_toTensor {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (z : ThickenedFunctions sY U) :
    MixedJet.sourceDerivative (toTensor sY U z) = coefficient sY U z := by
  simp [toTensor, coefficientLinear]

theorem toTensor_normalForm {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (a b : Functions sY U) :
    toTensor sY U (normalForm sY U a b) =
      (1 : MixedJet.Dual) ⊗ₜ[ℂ] a + Infinitesimal.epsilon ⊗ₜ[ℂ] b := by
  simp [toTensor, reductionFunctions, coefficientLinear]

theorem toTensor_injective {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    Function.Injective (toTensor sY U) := by
  intro z w h
  apply coefficients_ext sY U
  · simpa only [sourceZero_toTensor] using congrArg MixedJet.sourceZero h
  · simpa only [sourceDerivative_toTensor] using congrArg MixedJet.sourceDerivative h

theorem toTensor_surjective {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    Function.Surjective (toTensor sY U) := by
  intro w
  refine ⟨normalForm sY U (MixedJet.sourceZero (B := Functions sY U) w)
    (MixedJet.sourceDerivative (B := Functions sY U) w), ?_⟩
  rw [toTensor_normalForm]
  exact (MixedJet.source_reconstruct w).symm

/-- The comparison is an algebra equivalence, determined on all opens
by actual scheme functions, without a separate representability input. -/
def tensorEquiv {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    ThickenedFunctions sY U ≃ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] Functions sY U) :=
  AlgEquiv.ofBijective (toTensor sY U)
    ⟨toTensor_injective sY U, toTensor_surjective sY U⟩

theorem tensorEquiv_apply {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z : ThickenedFunctions sY U) : tensorEquiv sY U z = toTensor sY U z := rfl

theorem tensorEquiv_symm_apply {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (w : MixedJet.Dual ⊗[ℂ] Functions sY U) :
    (tensorEquiv sY U).symm w =
      normalForm sY U (MixedJet.sourceZero (B := Functions sY U) w)
        (MixedJet.sourceDerivative (B := Functions sY U) w) := by
  apply (tensorEquiv sY U).injective
  rw [AlgEquiv.apply_symm_apply, tensorEquiv_apply, toTensor_normalForm]
  exact MixedJet.source_reconstruct w

@[simp] theorem tensorEquiv_projection {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (a : Functions sY U) :
    tensorEquiv sY U ((projection sY).app U a) = (1 : MixedJet.Dual) ⊗ₜ[ℂ] a := by
  simp [tensorEquiv_apply, toTensor, reductionFunctions, coefficientLinear]

@[simp] theorem tensorEquiv_epsilon {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) :
    tensorEquiv sY U (epsilonOn sY U) =
      Infinitesimal.epsilon ⊗ₜ[ℂ] (1 : Functions sY U) := by
  simp [tensorEquiv_apply, toTensor, reductionFunctions, coefficientLinear]

@[simp] theorem reduction_tensorEquiv_symm {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (w : MixedJet.Dual ⊗[ℂ] Functions sY U) :
    reductionFunctions sY U ((tensorEquiv sY U).symm w) = MixedJet.sourceZero w := by
  rw [tensorEquiv_symm_apply]
  exact reductionCoefficient_normalForm sY U _ _

@[simp] theorem coefficient_tensorEquiv_symm {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (w : MixedJet.Dual ⊗[ℂ] Functions sY U) :
    coefficient sY U ((tensorEquiv sY U).symm w) = MixedJet.sourceDerivative w := by
  rw [tensorEquiv_symm_apply, coefficient_normalForm]

/-- The tensor comparison is uniquely normalized by the two original
scheme maps. This excludes a hidden rescaling of the source epsilon. -/
theorem tensorEquiv_unique {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (e : ThickenedFunctions sY U →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] Functions sY U))
    (hproj : ∀ a : Functions sY U,
      e ((projection sY).app U a) = (1 : MixedJet.Dual) ⊗ₜ[ℂ] a)
    (heps : e (epsilonOn sY U) =
      Infinitesimal.epsilon ⊗ₜ[ℂ] (1 : Functions sY U)) :
    e = (tensorEquiv sY U).toAlgHom := by
  ext z
  conv_lhs => rw [reconstruct sY U z]
  simp only [normalForm, map_add, map_mul, hproj, heps,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

theorem map_overC {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) :
    map g hg ≫ toC sZ = toC sY := by
  rw [toC, ← Category.assoc, map_projection, Category.assoc, hg]
  rfl

def sourcePullbackFunctions {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens) :
    ThickenedFunctions sZ U →ₐ[ℂ] ThickenedFunctions sY (g ⁻¹ᵁ U) :=
  onFunctionsLE (map g hg) (map_overC g hg)
    (projection sZ ⁻¹ᵁ U) (projection sY ⁻¹ᵁ (g ⁻¹ᵁ U))
    (map_projection_preimage g hg U).ge

theorem sourcePullbackFunctions_apply {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens)
    (z : ThickenedFunctions sZ U) :
    sourcePullbackFunctions g hg U z = sourcePullback g hg U z := rfl

/-- The geometric pullback is the actual tensor parameter change under
the normalized comparison, for arbitrary and nonreduced source schemes. -/
theorem tensorEquiv_sourcePullback {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens)
    (z : ThickenedFunctions sZ U) :
    tensorEquiv sY (g ⁻¹ᵁ U) (sourcePullbackFunctions g hg U z) =
      MixedJet.parameterChange (onFunctions g hg U) (tensorEquiv sZ U z) := by
  apply MixedJet.source_ext
  · rw [tensorEquiv_apply, sourceZero_toTensor,
      MixedJet.sourceZero_parameterChange, tensorEquiv_apply, sourceZero_toTensor]
    exact reductionCoefficient_sourcePullback g hg U z
  · rw [tensorEquiv_apply, sourceDerivative_toTensor,
      MixedJet.sourceDerivative_parameterChange, tensorEquiv_apply, sourceDerivative_toTensor]
    exact coefficient_sourcePullback g hg U z

theorem tensorEquiv_sourcePullback_hom {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens) :
    (tensorEquiv sY (g ⁻¹ᵁ U)).toAlgHom.comp (sourcePullbackFunctions g hg U) =
      (MixedJet.parameterChange (onFunctions g hg U)).comp
        (tensorEquiv sZ U).toAlgHom := by
  ext z
  exact tensorEquiv_sourcePullback g hg U z

/-- Restriction compatibility identifies the comparison on every open,
not merely the global sections of an affine source. -/
theorem tensorEquiv_restrict {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {U V : Y.Opens} (i : U ⟶ V) (z : ThickenedFunctions sY V) :
    tensorEquiv sY U ((space sY).presheaf.map
        (((TopologicalSpace.Opens.map (projection sY).base).map i).op) z) =
      MixedJet.parameterChange (SectionAlgebra.restrict sY i) (tensorEquiv sY V z) := by
  apply MixedJet.source_ext
  · rw [tensorEquiv_apply, sourceZero_toTensor,
      MixedJet.sourceZero_parameterChange, tensorEquiv_apply, sourceZero_toTensor]
    exact reductionCoefficient_restrict sY i z
  · rw [tensorEquiv_apply, sourceDerivative_toTensor,
      MixedJet.sourceDerivative_parameterChange, tensorEquiv_apply, sourceDerivative_toTensor]
    exact coefficient_restrict sY i z

end LeBrunSalamon.Construction.Lines.DualThickening

namespace LeBrunSalamon.Construction.Lines.FamilyVariation

open SectionAlgebra DualThickening

/-- The actual pullback of a family on the full central inverse-image open
with its proved complex algebra structure. -/
def Deformation.functionAlgebra {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) :
    Functions sX V →ₐ[ℂ] ThickenedFunctions sY (f ⁻¹ᵁ V) :=
  onFunctionsLE D.map D.overC V (projection sY ⁻¹ᵁ (f ⁻¹ᵁ V))
    (DualThickening.preimage_eq sY D.map f D.reduces V).ge

theorem Deformation.functionAlgebra_apply {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) (a : Functions sX V) :
    D.functionAlgebra V a = functionPullback sY D.map f D.reduces V a := rfl

/-- The algebra map into the actual tensor-product first jet is now
constructed from the original scheme family and the normalized comparison. -/
def Deformation.tensorFunctions {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) :
    Functions sX V →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] Functions sY (f ⁻¹ᵁ V)) :=
  (tensorEquiv sY (f ⁻¹ᵁ V)).toAlgHom.comp (D.functionAlgebra V)

/-- The constant coefficient is the specified central scheme map. -/
theorem Deformation.tensorFunctions_sourceZero {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) (a : Functions sX V) :
    MixedJet.sourceZero (D.tensorFunctions V a) = f.app V a := by
  change MixedJet.sourceZero
    (toTensor sY (f ⁻¹ᵁ V) (functionPullback sY D.map f D.reduces V a)) = _
  rw [sourceZero_toTensor, reductionCoefficient_functionPullback]

/-- The first coefficient is the original family derivation on functions. -/
theorem Deformation.tensorFunctions_sourceDerivative {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) (a : Functions sX V) :
    MixedJet.sourceDerivative (D.tensorFunctions V a) = D.onFunction V a := by
  exact sourceDerivative_toTensor sY (f ⁻¹ᵁ V)
    (functionPullback sY D.map f D.reduces V a)

def Deformation.onFunctionLinear {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) :
    Functions sX V →ₗ[ℂ] Functions sY (f ⁻¹ᵁ V) :=
  (coefficientLinear sY (f ⁻¹ᵁ V)).comp (D.functionAlgebra V).toLinearMap

theorem Deformation.onFunctionLinear_apply {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) (a : Functions sX V) :
    D.onFunctionLinear V a = D.onFunction V a := rfl

/-- The first-jet map is recovered from the actual central pullback and
the actual variation, not merely from its values at complex points. -/
theorem Deformation.tensorFunctions_reconstruct {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) (a : Functions sX V) :
    D.tensorFunctions V a =
      TensorProduct.tmul ℂ (M := MixedJet.Dual) (N := Functions sY (f ⁻¹ᵁ V))
        1 (f.app V a) +
      TensorProduct.tmul ℂ (M := MixedJet.Dual) (N := Functions sY (f ⁻¹ᵁ V))
        Infinitesimal.epsilon (D.onFunction V a) := by
  exact (MixedJet.source_reconstruct (D.tensorFunctions V a)).trans
    (congrArg₂ (fun u v : Functions sY (f ⁻¹ᵁ V) =>
      (1 : MixedJet.Dual) ⊗ₜ[ℂ] u + Infinitesimal.epsilon ⊗ₜ[ℂ] v)
      (D.tensorFunctions_sourceZero V a) (D.tensorFunctions_sourceDerivative V a))

/-- The tensor first jet changes its parameter by the original scheme
map; no separate identification is chosen after base change. -/
theorem Deformation.tensorFunctions_pullback {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (V : X.Opens) :
    (D.pullback g hg).tensorFunctions V =
      (MixedJet.parameterChange (onFunctions g hg (f ⁻¹ᵁ V))).comp
        (D.tensorFunctions V) := by
  ext a
  apply MixedJet.source_ext
  · rw [(D.pullback g hg).tensorFunctions_sourceZero]
    change (g ≫ f).app V a =
      MixedJet.sourceZero
        (MixedJet.parameterChange (onFunctions g hg (f ⁻¹ᵁ V))
          (D.tensorFunctions V a))
    rw [MixedJet.sourceZero_parameterChange, D.tensorFunctions_sourceZero]
    change (g ≫ f).app V a = g.app (f ⁻¹ᵁ V) (f.app V a)
    rw [Scheme.Hom.comp_app]
    rfl
  · rw [(D.pullback g hg).tensorFunctions_sourceDerivative]
    change (D.pullback g hg).onFunction V a =
      MixedJet.sourceDerivative
        (MixedJet.parameterChange (onFunctions g hg (f ⁻¹ᵁ V))
          (D.tensorFunctions V a))
    rw [MixedJet.sourceDerivative_parameterChange, D.tensorFunctions_sourceDerivative]
    exact D.pullback_onFunction g hg V a

/-- The actual regular coefficient is a complex linear map on local
target functions, and is natural for arbitrary parameter changes. -/
theorem Deformation.onFunctionLinear_pullback {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (V : X.Opens) :
    (D.pullback g hg).onFunctionLinear V =
      (onFunctions g hg (f ⁻¹ᵁ V)).toLinearMap.comp (D.onFunctionLinear V) := by
  ext a
  exact D.pullback_onFunction g hg V a

/-- The complete first jet of a constant family has zero linear term. -/
theorem constant_tensorFunctions {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (V : X.Opens) (a : Functions sX V) :
    (constant f hf).tensorFunctions V a =
      TensorProduct.tmul ℂ (M := MixedJet.Dual) (N := Functions sY (f ⁻¹ᵁ V))
        1 (f.app V a) := by
  rw [(constant f hf).tensorFunctions_reconstruct, constant_onFunction,
    TensorProduct.tmul_zero, add_zero]

/-- Fixed-source vanishing is retained after conversion into the actual
tensor algebra; this uses the scheme-theoretic fixed-source equation. -/
theorem Deformation.fixed_tensorFunctions {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (hfixed : D.IsFixedAlong g hg)
    (V : X.Opens) (a : Functions sX V) :
    MixedJet.parameterChange (onFunctions g hg (f ⁻¹ᵁ V))
        (D.tensorFunctions V a) =
      TensorProduct.tmul ℂ (M := MixedJet.Dual) (N := Functions sZ ((g ≫ f) ⁻¹ᵁ V))
        1 ((g ≫ f).app V a) := by
  have h := AlgHom.congr_fun (D.tensorFunctions_pullback g hg V) a
  rw [D.pullback_eq_constant_of_fixed g hg hfixed,
    constant_tensorFunctions] at h
  exact h.symm

/-- Target composition is formed on the original scheme map, with the
actual composite central map and its proved complex-base equation. -/
def Deformation.postcompose {Y X Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : X ⟶ Z) (hg : g ≫ sZ = sX) : Deformation sY sZ (f ≫ g) where
  map := D.map ≫ g
  overC := by rw [Category.assoc, hg, D.overC]
  reduces := by rw [← Category.assoc, D.reduces]

/-- The chain rule for the actual infinitesimal family coefficient. -/
theorem Deformation.postcompose_onFunction {Y X Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : X ⟶ Z) (hg : g ≫ sZ = sX)
    (W : Z.Opens) (a : Functions sZ W) :
    (D.postcompose g hg).onFunction W a = D.onFunction (g ⁻¹ᵁ W) (g.app W a) := by
  unfold Deformation.onFunction Deformation.postcompose
  rw [functionPullback_postcompose sY D.map f D.reduces g W]
  rfl

/-- Changing target coordinates is precomposition by the actual pullback
on functions, including the complete first-jet algebra map. -/
theorem Deformation.tensorFunctions_postcompose {Y X Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : X ⟶ Z) (hg : g ≫ sZ = sX) (W : Z.Opens) :
    (D.postcompose g hg).tensorFunctions W =
      (D.tensorFunctions (g ⁻¹ᵁ W)).comp (onFunctions g hg W) := by
  ext a
  apply MixedJet.source_ext
  · rw [(D.postcompose g hg).tensorFunctions_sourceZero]
    change (f ≫ g).app W a =
      MixedJet.sourceZero (D.tensorFunctions (g ⁻¹ᵁ W) (g.app W a))
    rw [D.tensorFunctions_sourceZero, Scheme.Hom.comp_app]
    rfl
  · rw [(D.postcompose g hg).tensorFunctions_sourceDerivative]
    change (D.postcompose g hg).onFunction W a =
      MixedJet.sourceDerivative (D.tensorFunctions (g ⁻¹ᵁ W) (g.app W a))
    rw [D.tensorFunctions_sourceDerivative]
    exact D.postcompose_onFunction g hg W a

theorem Deformation.onFunctionLinear_postcompose {Y X Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : X ⟶ Z) (hg : g ≫ sZ = sX) (W : Z.Opens) :
    (D.postcompose g hg).onFunctionLinear W =
      (D.onFunctionLinear (g ⁻¹ᵁ W)).comp (onFunctions g hg W).toLinearMap := by
  ext a
  exact D.postcompose_onFunction g hg W a

/-- Open restriction commutes with the actual tensor description, so
the comparison is already compatible on overlapping target charts. -/
theorem Deformation.tensorFunctions_restrict {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) {V W : X.Opens} (i : V ⟶ W) :
    (D.tensorFunctions V).comp (SectionAlgebra.restrict sX i) =
      (MixedJet.parameterChange
        (SectionAlgebra.restrict sY ((TopologicalSpace.Opens.map f.base).map i))).comp
        (D.tensorFunctions W) := by
  ext a
  apply MixedJet.source_ext
  · change MixedJet.sourceZero (D.tensorFunctions V (X.presheaf.map i.op a)) =
      MixedJet.sourceZero (MixedJet.parameterChange
        (SectionAlgebra.restrict sY ((TopologicalSpace.Opens.map f.base).map i))
        (D.tensorFunctions W a))
    rw [D.tensorFunctions_sourceZero, MixedJet.sourceZero_parameterChange,
      D.tensorFunctions_sourceZero]
    exact congrArg (fun k => k a) (f.naturality i.op)
  · change MixedJet.sourceDerivative (D.tensorFunctions V (X.presheaf.map i.op a)) =
      MixedJet.sourceDerivative (MixedJet.parameterChange
        (SectionAlgebra.restrict sY ((TopologicalSpace.Opens.map f.base).map i))
        (D.tensorFunctions W a))
    rw [D.tensorFunctions_sourceDerivative, MixedJet.sourceDerivative_parameterChange,
      D.tensorFunctions_sourceDerivative]
    exact (D.onFunction_restrict i a).symm

/-- Differentiating the source coefficient along a parameter tangent
equals the mixed coefficient of the actual restricted family functions. -/
theorem Deformation.tensorFunctions_mixedCoefficient {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens)
    (q : Functions sY (f ⁻¹ᵁ V) →ₐ[ℂ] ℂ)
    (v : Infinitesimal.Tangent (Functions sY (f ⁻¹ᵁ V)) q)
    (a : Functions sX V) :
    MixedJet.mixedCoeff
        (MixedJet.parameterChange (Infinitesimal.tangentToDual q v)
          (D.tensorFunctions V a)) = v.val (D.onFunction V a) := by
  rw [MixedJet.mixedCoeff_parameter_tangent, D.tensorFunctions_sourceDerivative]

/-- In the opposite order this is source differentiation of the actual
parameter deformation coefficient, in the full ring retaining z*epsilon. -/
theorem Deformation.tensorFunctions_derivativeExchange {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens)
    (q : Functions sY (f ⁻¹ᵁ V) →ₐ[ℂ] ℂ)
    (v : Infinitesimal.Tangent (Functions sY (f ⁻¹ᵁ V)) q)
    (a : Functions sX V) :
    MixedJet.dualCoefficient
        (MixedJet.parameterDerivative
          (MixedJet.parameterChange (Infinitesimal.tangentToDual q v)
            (D.tensorFunctions V a))) = v.val (D.onFunction V a) := by
  rw [← MixedJet.derivative_exchange]
  exact D.tensorFunctions_mixedCoefficient V q v a

end LeBrunSalamon.Construction.Lines.FamilyVariation

end

/-!
## The actual double thickening and interchange of infinitesimal coefficients

This module follows `dual_tensor_bridge` and `mixed_family_restriction`.
Its tensor factors are the two actual dual-number projections. The comparison
uses the canonical Gamma-Spec isomorphism, and the actual geometric swap is
proved to induce the tensor interchange. Local target functions are retained:
there is no global-functions test on the proper target variety.

Unchecked continuation; compilation is controlled by the 45,000-line gate.
No new admission is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.DualMixedBridge

open SectionAlgebra DualThickening

/-- Gamma-Spec on the actual dual-number scheme, with the specified
complex structure. Its algebra law is proved by Spec naturality. -/
def dualGlobalHom : Functions Infinitesimal.dualToC ⊤ →ₐ[ℂ] MixedJet.Dual where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom.hom
  commutes' := by
    intro c
    change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
      (complexConstants Infinitesimal.dualToC c) = algebraMap ℂ Infinitesimal.Dual c
    rw [complexConstants_apply_top]
    have h := congrArg (fun k => k c)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)))
    change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        (algebraMap ℂ Infinitesimal.Dual c) =
      Infinitesimal.dualToC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) at h
    rw [← h]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)) _

def dualGlobalEquiv : Functions Infinitesimal.dualToC ⊤ ≃ₐ[ℂ] MixedJet.Dual :=
  AlgEquiv.ofBijective dualGlobalHom
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom)

theorem dualGlobalEquiv_apply (a : Functions Infinitesimal.dualToC ⊤) :
    dualGlobalEquiv a = (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom a := rfl

theorem dualGlobalEquiv_symm_apply (a : MixedJet.Dual) :
    dualGlobalEquiv.symm a =
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv a := by
  apply dualGlobalEquiv.injective
  rw [AlgEquiv.apply_symm_apply, dualGlobalEquiv_apply]
  exact (Iso.inv_hom_id_apply
    (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)) a).symm

abbrev DoubleFunctions := Functions (DualThickening.toC Infinitesimal.dualToC) ⊤

/-- Actual global functions of the double thickening are the full mixed
jet ring. Epsilon from `parameter` is the first tensor factor. -/
def toMixed : DoubleFunctions ≃ₐ[ℂ] MixedJet.Mixed :=
  (tensorEquiv Infinitesimal.dualToC ⊤).trans
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : MixedJet.Dual ≃ₐ[ℂ] MixedJet.Dual) dualGlobalEquiv)

theorem toMixed_apply (z : DoubleFunctions) :
    toMixed z = MixedJet.parameterChange dualGlobalEquiv.toAlgHom
      (tensorEquiv Infinitesimal.dualToC ⊤ z) := rfl

theorem toMixed_reconstruct (z : DoubleFunctions) :
    toMixed z =
      (1 : MixedJet.Dual) ⊗ₜ[ℂ]
        dualGlobalEquiv (reductionCoefficient Infinitesimal.dualToC ⊤ z) +
      Infinitesimal.epsilon ⊗ₜ[ℂ]
        dualGlobalEquiv (coefficient Infinitesimal.dualToC ⊤ z) := by
  change MixedJet.parameterChange dualGlobalEquiv.toAlgHom
      ((1 : MixedJet.Dual) ⊗ₜ[ℂ] reductionFunctions Infinitesimal.dualToC ⊤ z +
        Infinitesimal.epsilon ⊗ₜ[ℂ] coefficientLinear Infinitesimal.dualToC ⊤ z) = _
  rw [map_add, MixedJet.parameterChange_tmul, MixedJet.parameterChange_tmul]
  rfl

@[simp] theorem toMixed_projection (a : Functions Infinitesimal.dualToC ⊤) :
    toMixed ((projection Infinitesimal.dualToC).appTop a) =
      (1 : MixedJet.Dual) ⊗ₜ[ℂ] dualGlobalEquiv a := by
  calc
    toMixed ((projection Infinitesimal.dualToC).appTop a) =
        MixedJet.parameterChange dualGlobalEquiv.toAlgHom
          (tensorEquiv Infinitesimal.dualToC ⊤
            ((projection Infinitesimal.dualToC).app ⊤ a)) := rfl
    _ = MixedJet.parameterChange dualGlobalEquiv.toAlgHom
        ((1 : MixedJet.Dual) ⊗ₜ[ℂ] a) :=
      congrArg (MixedJet.parameterChange dualGlobalEquiv.toAlgHom)
        (tensorEquiv_projection Infinitesimal.dualToC ⊤ a)
    _ = _ := MixedJet.parameterChange_tmul dualGlobalEquiv.toAlgHom 1 a

@[simp] theorem toMixed_epsilon :
    toMixed (epsilonOn Infinitesimal.dualToC ⊤) =
      Infinitesimal.epsilon ⊗ₜ[ℂ] (1 : MixedJet.Dual) := by
  rw [toMixed_apply, tensorEquiv_epsilon, MixedJet.parameterChange_tmul, map_one]

def parameterFunctions : Functions Infinitesimal.dualToC ⊤ →ₐ[ℂ] DoubleFunctions :=
  onFunctionsTop (parameter Infinitesimal.dualToC)
    (parameter_overC Infinitesimal.dualToC)

def parameterCoordinates : MixedJet.Dual →ₐ[ℂ] DoubleFunctions :=
  parameterFunctions.comp dualGlobalEquiv.symm.toAlgHom

theorem parameterCoordinates_epsilon :
    parameterCoordinates Infinitesimal.epsilon = epsilonOn Infinitesimal.dualToC ⊤ := by
  change (parameter Infinitesimal.dualToC).appTop
      (dualGlobalEquiv.symm Infinitesimal.epsilon) = _
  rw [dualGlobalEquiv_symm_apply]
  simp [epsilonOn]

/-- Both projections are normalized, not only their epsilon values. -/
theorem toMixed_parameterCoordinates (a : MixedJet.Dual) :
    toMixed (parameterCoordinates a) = a ⊗ₜ[ℂ] (1 : MixedJet.Dual) := by
  conv_lhs => rw [Infinitesimal.dual_normalForm_reconstruct a]
  simp only [map_add, map_mul, AlgHom.commutes, AlgEquiv.commutes,
    parameterCoordinates_epsilon, toMixed_epsilon,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]
  rw [← TensorProduct.add_tmul, ← Infinitesimal.dual_normalForm_reconstruct]

theorem toMixed_parameter (a : Functions Infinitesimal.dualToC ⊤) :
    toMixed ((parameter Infinitesimal.dualToC).appTop a) =
      dualGlobalEquiv a ⊗ₜ[ℂ] (1 : MixedJet.Dual) := by
  have h := toMixed_parameterCoordinates (dualGlobalEquiv a)
  change toMixed ((parameter Infinitesimal.dualToC).appTop
    (dualGlobalEquiv.symm (dualGlobalEquiv a))) = _ at h
  rw [AlgEquiv.symm_apply_apply] at h
  exact h

def swapFunctions : DoubleFunctions →ₐ[ℂ] DoubleFunctions :=
  onFunctionsTop MixedFamily.swap MixedFamily.swap_overC

theorem swapFunctions_projection (a : Functions Infinitesimal.dualToC ⊤) :
    swapFunctions ((projection Infinitesimal.dualToC).appTop a) =
      (parameter Infinitesimal.dualToC).appTop a := by
  change ((projection Infinitesimal.dualToC).appTop ≫ MixedFamily.swap.appTop) a = _
  rw [← Scheme.Hom.comp_appTop, MixedFamily.swap_projection]

theorem epsilon_top : epsilonOn Infinitesimal.dualToC ⊤ =
    (parameter Infinitesimal.dualToC).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon) := by
  simp [epsilonOn]

theorem swapFunctions_epsilon :
    swapFunctions (epsilonOn Infinitesimal.dualToC ⊤) =
      (projection Infinitesimal.dualToC).appTop
        (dualGlobalEquiv.symm Infinitesimal.epsilon) := by
  rw [epsilon_top, dualGlobalEquiv_symm_apply]
  change ((parameter Infinitesimal.dualToC).appTop ≫ MixedFamily.swap.appTop)
    ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon) = _
  rw [← Scheme.Hom.comp_appTop, MixedFamily.swap_parameter]

/-- The actual geometric interchange is the tensor-factor interchange
on every function of the full double thickening, including mixed terms. -/
theorem toMixed_swap (z : DoubleFunctions) :
    toMixed (swapFunctions z) =
      Algebra.TensorProduct.comm ℂ MixedJet.Dual MixedJet.Dual (toMixed z) := by
  let a : Functions Infinitesimal.dualToC ⊤ :=
    reductionCoefficient Infinitesimal.dualToC ⊤ z
  let b : Functions Infinitesimal.dualToC ⊤ :=
    coefficient Infinitesimal.dualToC ⊤ z
  have hz : z = normalForm Infinitesimal.dualToC ⊤ a b :=
    reconstruct Infinitesimal.dualToC ⊤ z
  rw [hz]
  let pa : DoubleFunctions := (projection Infinitesimal.dualToC).appTop a
  let pb : DoubleFunctions := (projection Infinitesimal.dualToC).appTop b
  let e : DoubleFunctions := epsilonOn Infinitesimal.dualToC ⊤
  change toMixed (swapFunctions (pa + e * pb)) =
    Algebra.TensorProduct.comm ℂ MixedJet.Dual MixedJet.Dual
      (toMixed (pa + e * pb))
  have ha : toMixed pa = (1 : MixedJet.Dual) ⊗ₜ[ℂ] dualGlobalEquiv a :=
    toMixed_projection a
  have hb : toMixed pb = (1 : MixedJet.Dual) ⊗ₜ[ℂ] dualGlobalEquiv b :=
    toMixed_projection b
  have he : toMixed e = Infinitesimal.epsilon ⊗ₜ[ℂ] (1 : MixedJet.Dual) :=
    toMixed_epsilon
  have ha' : toMixed (swapFunctions pa) = dualGlobalEquiv a ⊗ₜ[ℂ] (1 : MixedJet.Dual) :=
    (congrArg toMixed (swapFunctions_projection a)).trans (toMixed_parameter a)
  have hb' : toMixed (swapFunctions pb) = dualGlobalEquiv b ⊗ₜ[ℂ] (1 : MixedJet.Dual) :=
    (congrArg toMixed (swapFunctions_projection b)).trans (toMixed_parameter b)
  have he' : toMixed (swapFunctions e) = (1 : MixedJet.Dual) ⊗ₜ[ℂ] Infinitesimal.epsilon :=
    (congrArg toMixed swapFunctions_epsilon).trans
      ((toMixed_projection (dualGlobalEquiv.symm Infinitesimal.epsilon)).trans
        (congrArg (fun t : MixedJet.Dual => (1 : MixedJet.Dual) ⊗ₜ[ℂ] t)
          (dualGlobalEquiv.apply_symm_apply Infinitesimal.epsilon)))
  simp only [map_add, map_mul, ha, hb, he, ha', hb', he',
    Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one, Algebra.TensorProduct.comm_tmul]

theorem sourceDerivative_comm (w : MixedJet.Mixed) :
    MixedJet.sourceDerivative
      (Algebra.TensorProduct.comm ℂ MixedJet.Dual MixedJet.Dual w) =
        MixedJet.parameterDerivative w := by
  induction w using TensorProduct.inductionOn with
  | tmul a b => simp
  | add u v hu hv => simp only [map_add, hu, hv]

theorem mixedCoeff_comm (w : MixedJet.Mixed) :
    MixedJet.mixedCoeff
      (Algebra.TensorProduct.comm ℂ MixedJet.Dual MixedJet.Dual w) =
        MixedJet.mixedCoeff w := by
  change MixedJet.dualCoefficient
    (MixedJet.sourceDerivative
      (Algebra.TensorProduct.comm ℂ MixedJet.Dual MixedJet.Dual w)) = _
  rw [sourceDerivative_comm, ← MixedJet.derivative_exchange]
  rfl

/-- The actual mixed coefficient is a complex-linear functional on
functions of the genuine two-parameter infinitesimal scheme. -/
def mixedCoefficient : DoubleFunctions →ₗ[ℂ] ℂ :=
  MixedJet.mixedCoeff.comp toMixed.toLinearMap

/-- This formula identifies the functional with the two successive
actual normalized coefficients. -/
theorem mixedCoefficient_normalized (z : DoubleFunctions) :
    mixedCoefficient z = MixedJet.dualCoefficient
      (dualGlobalEquiv (coefficient Infinitesimal.dualToC ⊤ z)) := by
  change MixedJet.dualCoefficient (MixedJet.sourceDerivative (toMixed z)) = _
  rw [toMixed_apply, MixedJet.sourceDerivative_parameterChange,
    tensorEquiv_apply, sourceDerivative_toTensor]
  rfl

/-- The mixed infinitesimal functional is invariant under the actual
scheme swap, rather than an independently asserted equality of derivatives. -/
theorem mixedCoefficient_swap (z : DoubleFunctions) :
    mixedCoefficient (swapFunctions z) = mixedCoefficient z := by
  change MixedJet.mixedCoeff (toMixed (swapFunctions z)) = MixedJet.mixedCoeff (toMixed z)
  rw [toMixed_swap, mixedCoeff_comm]

/-- Local target pullbacks on the whole double thickening commute with
the actual swap. The support condition is solely the domain of the function. -/
theorem swap_appLE {X : Scheme} (F : MixedFamily.DoubleDual ⟶ X)
    (V : X.Opens) (hV : ⊤ ≤ F ⁻¹ᵁ V) :
    F.appLE V ⊤ hV ≫ MixedFamily.swap.appTop =
      (MixedFamily.swap ≫ F).appLE V ⊤
        (by intro y hy; exact hV trivial) := by
  change F.appLE V ⊤ hV ≫ MixedFamily.swap.app ⊤ = _
  rw [MixedFamily.swap.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rfl

/-- Equality of the two actual restrictions implies equality of mixed
coefficients of every local target function defined at their support. -/
theorem mixedCoefficient_restrictions {X : Scheme}
    (F G : MixedFamily.DoubleDual ⟶ X) (hFG : F = MixedFamily.swap ≫ G)
    (V : X.Opens) (hG : ⊤ ≤ G ⁻¹ᵁ V)
    (hF : ⊤ ≤ F ⁻¹ᵁ V) (a : RingSections X V) :
    mixedCoefficient (F.appLE V ⊤ hF a) =
      mixedCoefficient (G.appLE V ⊤ hG a) := by
  have hp := congrArg (fun k => k a) (swap_appLE G V hG)
  rw [← DualThickening.appLE_of_map_eq hFG V ⊤ hF _] at hp
  change swapFunctions (G.appLE V ⊤ hG a) = F.appLE V ⊤ hF a at hp
  rw [← hp, mixedCoefficient_swap]

/-- The actual infinitesimal source lift has image in the full target
function domain whenever its central map does. Nilpotent topology supplies
this equality of inverse-image opens. -/
theorem actualPullback_support {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : FamilyVariation.Deformation sY sX f)
    (g : Infinitesimal.DualScheme ⟶ Y) (hg : g ≫ sY = Infinitesimal.dualToC)
    (V : X.Opens) (hV : ⊤ ≤ g ⁻¹ᵁ (f ⁻¹ᵁ V)) :
    ⊤ ≤ (D.pullback g hg).map ⁻¹ᵁ V := by
  rw [DualThickening.preimage_eq Infinitesimal.dualToC
    (D.pullback g hg).map (g ≫ f) (D.pullback g hg).reduces V]
  intro y hy
  exact hV trivial

/-- The mixed coefficient of an actual pulled-back family is source
differentiation of its original infinitesimal variation on the local target
function. Only the actual source lift and actual function domain are inputs. -/
theorem mixedCoefficient_actualPullback {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : FamilyVariation.Deformation sY sX f)
    (g : Infinitesimal.DualScheme ⟶ Y) (hg : g ≫ sY = Infinitesimal.dualToC)
    (V : X.Opens) (hV : ⊤ ≤ g ⁻¹ᵁ (f ⁻¹ᵁ V)) (a : RingSections X V) :
    mixedCoefficient
        ((D.pullback g hg).map.appLE V ⊤ (actualPullback_support D g hg V hV) a) =
      MixedJet.dualCoefficient
        (dualGlobalEquiv (g.appLE (f ⁻¹ᵁ V) ⊤ hV (D.onFunction V a))) := by
  let D' := D.pullback g hg
  let U : Infinitesimal.DualScheme.Opens := (g ≫ f) ⁻¹ᵁ V
  have hU : ⊤ ≤ U := hV
  have hrestrict : functionPullback Infinitesimal.dualToC D'.map (g ≫ f) D'.reduces V ≫
      MixedFamily.DoubleDual.presheaf.map
        (((TopologicalSpace.Opens.map (projection Infinitesimal.dualToC).base).map
          (homOfLE hU)).op) =
      D'.map.appLE V ⊤ (actualPullback_support D g hg V hV) := by
    unfold functionPullback
    rw [Scheme.Hom.appLE_map]
    rfl
  have hc := coefficient_restrict Infinitesimal.dualToC (homOfLE hU)
    (functionPullback Infinitesimal.dualToC D'.map (g ≫ f) D'.reduces V a)
  have hr := congrArg (fun k => k a) hrestrict
  change MixedFamily.DoubleDual.presheaf.map
      (((TopologicalSpace.Opens.map (projection Infinitesimal.dualToC).base).map
        (homOfLE hU)).op)
      (functionPullback Infinitesimal.dualToC D'.map (g ≫ f) D'.reduces V a) =
    D'.map.appLE V ⊤ (actualPullback_support D g hg V hV) a at hr
  rw [hr] at hc
  change coefficient Infinitesimal.dualToC ⊤
      (D'.map.appLE V ⊤ (actualPullback_support D g hg V hV) a) =
    Infinitesimal.DualScheme.presheaf.map (homOfLE hU).op
      (D'.onFunction V a) at hc
  rw [D.pullback_onFunction g hg] at hc
  rw [mixedCoefficient_normalized, hc]
  rfl

end LeBrunSalamon.Construction.Lines.DualMixedBridge

end

/-!
## The velocity morphism over the whole fixed-node Hom parameter

The parameter scheme is arbitrary. The coefficient of the actual source
first jet gives a derivation into its global functions. The Gamma--Spec
adjunction then constructs an actual scheme morphism to the affine scheme
representing point derivations. A single actual affine target neighborhood
is sufficient, since the first jet has the fixed point as its topological
support. This factorization is proved using the nilpotent-thickening
topology, without replacing the family by its reduction on functions.

All function identities below retain the original target chart and the
actual source first jet. The identification with the original tangent
sheaf fiber is a separate comparison; the representing vector space is
not silently identified by an arbitrary vector-space isomorphism.

STATUS: unchecked continuation after LSHomVelocity and the all-open
SectionAlgebra construction. Check when the master reaches 45,000 lines.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.GlobalVelocity

open FamilyVariation

section GlobalFunctions

variable {A B : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B]

/-- The Gamma--Spec comparison carries the original algebra constants
to the constants defined by the actual complex structure map. -/
theorem specFunction_constant (c : ℂ) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap ℂ A c) =
      complexConstants (DirectionCones.affineBaseMap A) c := by
  rw [complexConstants_apply_top]
  exact congrArg (fun k : CommRingCat.of ℂ ⟶
    (Spec (CommRingCat.of A)).presheaf.obj (op ⊤) => k c)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap ℂ A)))

/-- Actual affine functions, regarded as global functions with their
specified complex scalar structure. -/
def specFunctions (A : Type) [CommRing A] [Algebra ℂ A] :
    A →ₐ[ℂ] SectionAlgebra.Functions (DirectionCones.affineBaseMap A) ⊤ where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  commutes' := specFunction_constant

@[simp] theorem specFunctions_apply (a : A) :
    specFunctions A a = (Scheme.ΓSpecIso (CommRingCat.of A)).inv a := rfl

/-- A map to an affine scheme obtained from the actual global functions.
No affineness, finite-type, reducedness, or smoothness of Y is assumed. -/
def toSpec {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (φ : A →ₐ[ℂ] SectionAlgebra.Functions sY ⊤) :
    Y ⟶ Spec (CommRingCat.of A) :=
  (ΓSpec.adjunction.homEquiv Y (op (CommRingCat.of A)))
    (CommRingCat.ofHom φ.toRingHom).op

/-- This formula specifies the complete comorphism, not merely its
values at complex parameter points. -/
theorem toSpec_function {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (φ : A →ₐ[ℂ] SectionAlgebra.Functions sY ⊤) (a : A) :
    (toSpec φ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = φ a := by
  exact congrArg (fun k : CommRingCat.of A ⟶ Y.presheaf.obj (op ⊤) => k a)
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom φ.toRingHom))

theorem toSpec_overC {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (φ : A →ₐ[ℂ] SectionAlgebra.Functions sY ⊤) :
    toSpec φ ≫ DirectionCones.affineBaseMap A = sY := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext c
  change (toSpec φ).appTop
    ((DirectionCones.affineBaseMap A).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) =
    sY.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  rw [← complexConstants_apply_top, ← specFunction_constant, toSpec_function,
    ← complexConstants_apply_top]
  change φ (algebraMap ℂ A c) = complexConstants sY c
  exact φ.commutes c

/-- A map to the represented affine scheme is uniquely fixed by these
function pullbacks, including on nonreduced test schemes. -/
theorem toSpec_unique {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (φ : A →ₐ[ℂ] SectionAlgebra.Functions sY ⊤)
    (f : Y ⟶ Spec (CommRingCat.of A))
    (hf : ∀ a : A,
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = φ a) :
    f = toSpec φ := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext a
  exact (hf a).trans (toSpec_function φ a).symm

theorem toSpec_precompose {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (φ : A →ₐ[ℂ] SectionAlgebra.Functions sY ⊤)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    g ≫ toSpec φ =
      toSpec ((SectionAlgebra.onFunctionsTop g hg).comp φ) := by
  apply toSpec_unique
  intro a
  change g.appTop ((toSpec φ).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = _
  rw [toSpec_function]
  rfl

/-- On an affine parameter scheme this recovers exactly Spec of the
specified algebra homomorphism. -/
theorem toSpec_specFunctions (φ : A →ₐ[ℂ] B) :
    toSpec ((specFunctions B).comp φ) = DirectionCones.affineMap φ := by
  symm
  apply toSpec_unique
  intro a
  exact (congrArg (fun k : CommRingCat.of A ⟶
    (Spec (CommRingCat.of B)).presheaf.obj (op ⊤) => k a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))).symm

/-- The same construction with the identity global algebra map is the
canonical affinization morphism from mathlib. -/
theorem toSpec_id {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    toSpec (AlgHom.id ℂ (SectionAlgebra.Functions sY ⊤)) = Y.toSpecΓ := by
  symm
  apply toSpec_unique (A := SectionAlgebra.Functions sY ⊤)
    (AlgHom.id ℂ (SectionAlgebra.Functions sY ⊤))
  intro a
  rw [Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (Y.presheaf.obj (op ⊤))) a

theorem toSpecΓ_overC {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    Y.toSpecΓ ≫
      DirectionCones.affineBaseMap (SectionAlgebra.Functions sY ⊤) = sY := by
  rw [← toSpec_id sY]
  exact toSpec_overC (AlgHom.id ℂ (SectionAlgebra.Functions sY ⊤))

/-- The affine chart's rational point is obtained from its actual map
Spec C -> Spec A. It is not an independently chosen evaluation. -/
def specPoint (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase) : A →ₐ[ℂ] ℂ where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp
    (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  commutes' := by
    intro c
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap ℂ A c))) = c
    rw [specFunction_constant,
      complexConstants_naturality q (𝟙 ComplexBase) (DirectionCones.affineBaseMap A) hq,
      complexConstants_apply_top]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) c

theorem specPoint_function (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase) (a : A) :
    q.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (specPoint q hq a) := by
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ))
    (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))).symm

/-- The normalized coordinate point defines the very same scheme map. -/
theorem affineMap_specPoint (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase) :
    DirectionCones.affineMap (specPoint q hq) = q := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext a
  have hn := congrArg (fun k : CommRingCat.of A ⟶
    ComplexBase.presheaf.obj (op ⊤) => k a)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (specPoint q hq).toRingHom))
  exact hn.symm.trans (specPoint_function q hq a).symm

theorem constantMap_function {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase) (a : A) :
    (sY ≫ q).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
      complexConstants sY (specPoint q hq a) := by
  change sY.appTop (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = _
  rw [specPoint_function, complexConstants_apply_top]

end GlobalFunctions

section CoefficientMorphisms

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable {Y : Scheme} {sY : Y ⟶ ComplexBase}

/-- The actual first-jet coefficient on the target affine coordinate
ring. Its values are global functions of the whole parameter scheme. -/
def coefficient {f : Y ⟶ Spec (CommRingCat.of A)}
    (D : Deformation sY (DirectionCones.affineBaseMap A) f) :
    A →ₗ[ℂ] SectionAlgebra.Functions sY ⊤ :=
  (D.onFunctionLinear ⊤).comp (specFunctions A).toLinearMap

@[simp] theorem coefficient_apply {f : Y ⟶ Spec (CommRingCat.of A)}
    (D : Deformation sY (DirectionCones.affineBaseMap A) f) (a : A) :
    coefficient D a = D.onFunction ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := rfl

theorem coefficient_leibniz (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q)) (a b : A) :
    coefficient D (a*b) =
      specPoint q hq a • coefficient D b + specPoint q hq b • coefficient D a := by
  let da : RingSections Y ⊤ := D.onFunction ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
  let db : RingSections Y ⊤ := D.onFunction ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b)
  change (D.onFunction ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (a*b)) :
      RingSections Y ⊤) =
    complexConstants sY (specPoint q hq a) * db + complexConstants sY (specPoint q hq b) * da
  rw [map_mul, D.onFunction_leibniz]
  exact congrArg₂ (fun u v : RingSections Y ⊤ => u * db + v * da)
    (constantMap_function sY q hq a) (constantMap_function sY q hq b)

/-- The actual velocity comorphism is defined by all differential
coordinates. This algebra homomorphism exists over the whole parameter. -/
def velocityComorphism (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q)) :
    AffineVelocity.CoordinateRing (specPoint q hq) →ₐ[ℂ]
      SectionAlgebra.Functions sY ⊤ :=
  AffineVelocity.coordinateLift (specPoint q hq) (coefficient D)
    (coefficient_leibniz q hq D)

@[simp] theorem velocityComorphism_coordinate
    (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q)) (a : A) :
    velocityComorphism q hq D (AffineVelocity.coordinate (specPoint q hq) a) =
      coefficient D a :=
  AffineVelocity.coordinateLift_coordinate (specPoint q hq) _ _ a

/-- The global velocity morphism obtained from the genuine source-first-jet
family. The source Y is not assumed affine. -/
def velocityMorphism (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q)) :
    Y ⟶ AffineVelocity.tangentScheme (specPoint q hq) :=
  toSpec (velocityComorphism q hq D)

theorem velocityMorphism_overC (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q)) :
    velocityMorphism q hq D ≫ AffineVelocity.tangentSchemeToC (specPoint q hq) = sY :=
  toSpec_overC (velocityComorphism q hq D)

/-- The full normalization on the coordinate algebra. -/
theorem velocityMorphism_function (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (r : AffineVelocity.CoordinateRing (specPoint q hq)) :
    (velocityMorphism q hq D).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of
        (AffineVelocity.CoordinateRing (specPoint q hq)))).inv r) =
      velocityComorphism q hq D r :=
  toSpec_function (velocityComorphism q hq D) r

/-- Each linear coordinate is the actual epsilon coefficient of the
original map's pullback on functions. -/
theorem velocityMorphism_coordinate (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q)) (a : A) :
    (velocityMorphism q hq D).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of
        (AffineVelocity.CoordinateRing (specPoint q hq)))).inv
          (AffineVelocity.coordinate (specPoint q hq) a)) =
      D.onFunction ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := by
  rw [velocityMorphism_function, velocityComorphism_coordinate]
  rfl

/-- The same coordinate is the value of the actual cotangent functional
constructed from the family, with no separate tangent identification. -/
theorem velocityMorphism_cotangent (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q)) (a : A) :
    (velocityMorphism q hq D).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of
        (AffineVelocity.CoordinateRing (specPoint q hq)))).inv
          (AffineVelocity.coordinate (specPoint q hq) a)) =
      D.cotangentHom.app ⊤
        (pullLocalSection (sY ≫ q) (cotangentSheaf (DirectionCones.affineBaseMap A)) ⊤
          ((cotangentPresentation (DirectionCones.affineBaseMap A)).differential.apply ⊤
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) := by
  rw [velocityMorphism_coordinate]
  exact (D.cotangentHom_differential ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)).symm

/-- Transport only an equality of central maps. The actual family is
kept literally unchanged. -/
def recenter {X : Scheme} {sX : X ⟶ ComplexBase} {f g : Y ⟶ X}
    (D : Deformation sY sX f) (h : f = g) : Deformation sY sX g where
  map := D.map
  overC := D.overC
  reduces := D.reduces.trans h

@[simp] theorem recenter_onFunction_top {X : Scheme} {sX : X ⟶ ComplexBase}
    {f g : Y ⟶ X} (D : Deformation sY sX f) (h : f = g)
    (a : RingSections X ⊤) : (recenter D h).onFunction ⊤ a = D.onFunction ⊤ a := by
  subst g
  rfl

/-- The actual parameter restriction, normalized at the same target
point. This uses only the given over-C equation of the parameter map. -/
def parameterChange {Z : Scheme} {sZ : Z ⟶ ComplexBase}
    (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    Deformation sZ (DirectionCones.affineBaseMap A) (sZ ≫ q) :=
  recenter (D.pullback g hg) (by rw [← Category.assoc, hg])

theorem coefficient_parameterChange {Z : Scheme} {sZ : Z ⟶ ComplexBase}
    (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (a : A) :
    coefficient (parameterChange q D g hg) a =
      g.appTop (coefficient D a) := by
  change (recenter (D.pullback g hg) _).onFunction ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = _
  rw [recenter_onFunction_top, D.pullback_onFunction]
  rfl

theorem velocityComorphism_parameterChange {Z : Scheme} {sZ : Z ⟶ ComplexBase}
    (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    velocityComorphism q hq (parameterChange q D g hg) =
      (SectionAlgebra.onFunctionsTop g hg).comp (velocityComorphism q hq D) := by
  apply AffineVelocity.coordinate_ext (specPoint q hq)
  intro a
  rw [velocityComorphism_coordinate]
  change coefficient (parameterChange q D g hg) a =
    g.appTop (velocityComorphism q hq D (AffineVelocity.coordinate (specPoint q hq) a))
  rw [velocityComorphism_coordinate, coefficient_parameterChange]

/-- Naturality holds as an equality of scheme morphisms for arbitrary
test schemes, including dual-number parameter changes. -/
theorem velocityMorphism_parameterChange {Z : Scheme} {sZ : Z ⟶ ComplexBase}
    (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    g ≫ velocityMorphism q hq D =
      velocityMorphism q hq (parameterChange q D g hg) := by
  change g ≫ toSpec (velocityComorphism q hq D) = _
  rw [toSpec_precompose, ← velocityComorphism_parameterChange]
  rfl

end CoefficientMorphisms

section ActualAffineComparison

open scoped TensorProduct

variable {A B : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B]
variable {Y : Scheme} {sY : Y ⟶ ComplexBase}

/-- The particular tensor-algebra first jet supplied by the actual
scheme family and the normalized function comparison. -/
def firstJetAlgebra {f : Y ⟶ Spec (CommRingCat.of A)}
    (D : Deformation sY (DirectionCones.affineBaseMap A) f) :
    A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] SectionAlgebra.Functions sY ⊤) :=
  (D.tensorFunctions ⊤).comp (specFunctions A)

theorem firstJetAlgebra_fixedNode (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q)) :
    AffineVelocity.IsFixedNode (firstJetAlgebra D) (specPoint q hq) := by
  apply AlgHom.ext
  intro a
  change MixedJet.sourceZero
    (D.tensorFunctions ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
      algebraMap ℂ (SectionAlgebra.Functions sY ⊤) (specPoint q hq a)
  rw [D.tensorFunctions_sourceZero, SectionAlgebra.algebraMap_top]
  exact constantMap_function sY q hq a

theorem firstJetAlgebra_sourceDerivative {f : Y ⟶ Spec (CommRingCat.of A)}
    (D : Deformation sY (DirectionCones.affineBaseMap A) f) (a : A) :
    MixedJet.sourceDerivative (firstJetAlgebra D a) = coefficient D a :=
  D.tensorFunctions_sourceDerivative ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)

/-- The new global morphism and the previously constructed affine
velocity use precisely the same algebra homomorphism. -/
theorem velocityComorphism_eq_affine (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q)) :
    velocityComorphism q hq D =
      AffineVelocity.velocityComorphism (firstJetAlgebra D) (specPoint q hq)
        (firstJetAlgebra_fixedNode q hq D) := by
  apply AffineVelocity.coordinate_ext (specPoint q hq)
  intro a
  rw [velocityComorphism_coordinate, AffineVelocity.velocityComorphism_coordinate,
    firstJetAlgebra_sourceDerivative]

/-- Pull functions from the arbitrary parameter Y to a specified affine
parameter chart and use that chart's canonical Gamma--Spec comparison. -/
def affineParameterFunctions
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B) :
    SectionAlgebra.Functions sY ⊤ →ₐ[ℂ] B where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp g.appTop.hom
  commutes' := by
    intro c
    change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      (g.appTop (complexConstants sY c)) = algebraMap ℂ B c
    rw [complexConstants_naturality g (DirectionCones.affineBaseMap B) sY hg,
      ← specFunction_constant]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) _

/-- Normalization of the actual affine parameter pullback on functions. -/
theorem affineParameterFunctions_normalized
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B)
    (b : SectionAlgebra.Functions sY ⊤) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv
      (affineParameterFunctions g hg b) = g.appTop b :=
  Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) _

/-- The affine parameter jet is now derived from the actual family,
rather than supplied as an arbitrary first-jet algebra map. -/
def affineParameterJet {f : Y ⟶ Spec (CommRingCat.of A)}
    (D : Deformation sY (DirectionCones.affineBaseMap A) f)
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B) :
    A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B) :=
  (MixedJet.parameterChange (affineParameterFunctions g hg)).comp (firstJetAlgebra D)

theorem affineParameterJet_fixedNode (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B) :
    AffineVelocity.IsFixedNode (affineParameterJet D g hg) (specPoint q hq) :=
  AffineVelocity.parameterChange_fixedNode (firstJetAlgebra D) (specPoint q hq)
    (firstJetAlgebra_fixedNode q hq D) (affineParameterFunctions g hg)

theorem affineParameterJet_sourceDerivative {f : Y ⟶ Spec (CommRingCat.of A)}
    (D : Deformation sY (DirectionCones.affineBaseMap A) f)
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B) (a : A) :
    MixedJet.sourceDerivative (affineParameterJet D g hg a) =
      affineParameterFunctions g hg (coefficient D a) := by
  change MixedJet.sourceDerivative
    (MixedJet.parameterChange (affineParameterFunctions g hg) (firstJetAlgebra D a)) = _
  rw [MixedJet.sourceDerivative_parameterChange, firstJetAlgebra_sourceDerivative]

/-- Restricting the global velocity along an actual affine parameter
chart gives exactly the already constructed affine velocity morphism.
This equality is proved on its full coordinate algebra. -/
theorem velocityMorphism_affineParameter
    (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B) :
    g ≫ velocityMorphism q hq D =
      AffineVelocity.velocityMorphism (affineParameterJet D g hg) (specPoint q hq)
        (affineParameterJet_fixedNode q hq D g hg) := by
  change g ≫ toSpec (velocityComorphism q hq D) =
    DirectionCones.affineMap
      (AffineVelocity.velocityComorphism (affineParameterJet D g hg) (specPoint q hq)
        (affineParameterJet_fixedNode q hq D g hg))
  rw [← toSpec_specFunctions
    (AffineVelocity.velocityComorphism (affineParameterJet D g hg) (specPoint q hq)
      (affineParameterJet_fixedNode q hq D g hg))]
  change g ≫ toSpec (velocityComorphism q hq D) = _
  rw [toSpec_precompose (velocityComorphism q hq D) g hg]
  congr 1
  apply AffineVelocity.coordinate_ext (specPoint q hq)
  intro a
  change g.appTop (velocityComorphism q hq D (AffineVelocity.coordinate (specPoint q hq) a)) =
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv
      (AffineVelocity.velocityComorphism (affineParameterJet D g hg) (specPoint q hq)
        (affineParameterJet_fixedNode q hq D g hg)
        (AffineVelocity.coordinate (specPoint q hq) a))
  rw [velocityComorphism_coordinate, AffineVelocity.velocityComorphism_coordinate,
    affineParameterJet_sourceDerivative D g hg, affineParameterFunctions_normalized g hg]

/-- The actual derivative of that affine-chart restriction, expressed
in the previously normalized linear coordinates on its target. -/
def affineDifferential (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B) (b : B →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent B b →ₗ[ℂ] Infinitesimal.Tangent A (specPoint q hq) :=
  AffineVelocity.velocityDifferential (affineParameterJet D g hg) (specPoint q hq)
    (affineParameterJet_fixedNode q hq D g hg) b

/-- Differentiation acts on the actual coefficient function pulled back
from the global parameter scheme. -/
theorem affineDifferential_apply (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B) (b : B →ₐ[ℂ] ℂ)
    (v : Infinitesimal.Tangent B b) (a : A) :
    (affineDifferential q hq D g hg b v).val a =
      v.val (affineParameterFunctions g hg (coefficient D a)) := by
  unfold affineDifferential
  rw [AffineVelocity.velocityDifferential_apply, affineParameterJet_sourceDerivative]

/-- The mixed derivative formula is now attached to the differential
of the actual global velocity restricted to an actual affine chart. -/
theorem affineDifferential_eq_mixedCoefficient
    (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B) (b : B →ₐ[ℂ] ℂ)
    (v : Infinitesimal.Tangent B b) (a : A) :
    (affineDifferential q hq D g hg b v).val a =
      MixedJet.mixedCoeff
        (MixedJet.parameterChange (Infinitesimal.tangentToDual b v)
          (affineParameterJet D g hg a)) := by
  unfold affineDifferential
  rw [AffineVelocity.velocityDifferential_apply]
  exact (MixedJet.velocity_function_differential (affineParameterJet D g hg) b v a).symm

/-- Interchanging the two actual first-order restrictions gives source
differentiation of the parameter variation. The mixed term is retained. -/
theorem affineDifferential_eq_deformationDerivative
    (q : ComplexBase ⟶ Spec (CommRingCat.of A))
    (hq : q ≫ DirectionCones.affineBaseMap A = 𝟙 ComplexBase)
    (D : Deformation sY (DirectionCones.affineBaseMap A) (sY ≫ q))
    (g : Spec (CommRingCat.of B) ⟶ Y)
    (hg : g ≫ sY = DirectionCones.affineBaseMap B) (b : B →ₐ[ℂ] ℂ)
    (v : Infinitesimal.Tangent B b) :
    (affineDifferential q hq D g hg b v).val =
      MixedJet.dualCoefficient.comp
        (MixedJet.deformationOverSource
          (AffineVelocity.parameterJet (affineParameterJet D g hg) b v)) :=
  AffineVelocity.velocityDifferential_eq_deformationDerivative
    (affineParameterJet D g hg) (specPoint q hq)
    (affineParameterJet_fixedNode q hq D g hg) b v

end ActualAffineComparison

section LocalTargetFunctions

variable {Y Z : Scheme} {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
variable {f : Y ⟶ Z}

/-- If the central map is supported in an open, so is the entire actual
dual-number family. This is a statement about underlying points only. -/
theorem family_preimage_top (D : Deformation sY sZ f) (V : Z.Opens)
    (hV : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ V) :
    (⊤ : (DualThickening.space sY).Opens) ≤ D.map ⁻¹ᵁ V := by
  intro y _
  change D.map y ∈ V
  rw [DualThickening.family_apply_eq_centre sY D.map f D.reduces]
  exact hV (show DualThickening.projection sY y ∈ (⊤ : Y.Opens) by trivial)

/-- Coefficient of an original local target function on the whole
parameter scheme. The function pullback is the actual appLE map of D. -/
def localCoefficient (D : Deformation sY sZ f) (V : Z.Opens)
    (hV : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ V) (a : RingSections Z V) :
    SectionAlgebra.Functions sY ⊤ :=
  DualThickening.coefficient sY ⊤
    (D.map.appLE V ⊤ (family_preimage_top D V hV) a)

/-- This coefficient is exactly the restriction of the previously
constructed relative derivation on the same local target function. -/
theorem localCoefficient_onFunction (D : Deformation sY sZ f) (V : Z.Opens)
    (hV : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ V) (a : RingSections Z V) :
    localCoefficient D V hV a =
      Y.presheaf.map (homOfLE hV).op (D.onFunction V a) := by
  have hm : DualThickening.functionPullback sY D.map f D.reduces V ≫
      (DualThickening.space sY).presheaf.map
        (((TopologicalSpace.Opens.map (DualThickening.projection sY).base).map
          (homOfLE hV)).op) =
      D.map.appLE V ⊤ (family_preimage_top D V hV) := by
    unfold DualThickening.functionPullback
    rw [Scheme.Hom.appLE_map]
    rfl
  unfold localCoefficient
  rw [← hm]
  exact DualThickening.coefficient_restrict sY (homOfLE hV)
    (DualThickening.functionPullback sY D.map f D.reduces V a)

/-- Normalization against the ORIGINAL cotangent sheaf on every local
target function. The only restriction is the actual full-support inclusion. -/
theorem localCoefficient_cotangent (D : Deformation sY sZ f) (V : Z.Opens)
    (hV : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ V) (a : RingSections Z V) :
    localCoefficient D V hV a =
      Y.presheaf.map (homOfLE hV).op
        (D.cotangentHom.app (f ⁻¹ᵁ V)
          (pullLocalSection f (cotangentSheaf sZ) V
            ((cotangentPresentation sZ).differential.apply V a))) := by
  rw [D.cotangentHom_differential, localCoefficient_onFunction]

theorem onFunction_top (D : Deformation sY sZ f) (a : RingSections Z ⊤) :
    D.onFunction ⊤ a = DualThickening.coefficient sY ⊤ (D.map.appTop a) := by
  unfold Deformation.onFunction DualThickening.functionPullback
  change DualThickening.coefficient sY ⊤
      (D.map.appLE ⊤ (D.map ⁻¹ᵁ ⊤) le_rfl a) =
    DualThickening.coefficient sY ⊤ (D.map.appTop a)
  exact congrArg (DualThickening.coefficient sY ⊤)
    (congrArg (fun k => k a) (D.map.appLE_eq_app (U := ⊤)))

end LocalTargetFunctions

section ActualTargetCharts

variable {d : ℕ} (X : SmoothProperComplexVariety d) (x : ComplexPoint X)

/-- An actual affine target neighborhood with its complex structure and
its actual lift of the specified point. No tangent comparison is a field. -/
structure TargetChart where
  Ring : Type
  [commRing : CommRing Ring]
  [algebra : Algebra ℂ Ring]
  inclusion : Spec (CommRingCat.of Ring) ⟶ X.scheme
  [openImmersion : IsOpenImmersion inclusion]
  overC : inclusion ≫ X.structureMap = DirectionCones.affineBaseMap Ring
  point : ComplexBase ⟶ Spec (CommRingCat.of Ring)
  atPoint : point ≫ inclusion = x.map

attribute [instance] TargetChart.commRing TargetChart.algebra TargetChart.openImmersion

namespace TargetChart

variable {X x} (C : TargetChart X x)

theorem point_overC : C.point ≫ DirectionCones.affineBaseMap C.Ring =
    𝟙 ComplexBase := by
  rw [← C.overC, ← Category.assoc, C.atPoint, x.overC]

def evaluation : C.Ring →ₐ[ℂ] ℂ := specPoint C.point C.point_overC

/-- Every actual first jet centered at x has its entire topological image
inside this chart. Its nonconstant pullback on functions is retained. -/
theorem family_range {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map)) :
    Set.range D.map ⊆ Set.range C.inclusion := by
  rintro _ ⟨z, rfl⟩
  refine ⟨C.point (sY (DualThickening.projection sY z)), ?_⟩
  change (C.point ≫ C.inclusion) (sY (DualThickening.projection sY z)) = D.map z
  rw [C.atPoint, DualThickening.family_apply_eq_centre sY D.map
    (sY ≫ x.map) D.reduces]
  rfl

def familyMap {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map)) :
    DualThickening.space sY ⟶ Spec (CommRingCat.of C.Ring) :=
  IsOpenImmersion.lift C.inclusion D.map (C.family_range D)

@[simp] theorem familyMap_inclusion {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map)) :
    C.familyMap D ≫ C.inclusion = D.map :=
  IsOpenImmersion.lift_fac _ _ _

/-- The affine first-jet family is factored from the specified family.
Both its base equation and its reduction follow from the actual maps. -/
def deformation {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map)) :
    Deformation sY (DirectionCones.affineBaseMap C.Ring) (sY ≫ C.point) where
  map := C.familyMap D
  overC := by
    rw [← C.overC, ← Category.assoc, C.familyMap_inclusion, D.overC]
  reduces := by
    apply (cancel_mono C.inclusion).mp
    rw [Category.assoc, C.familyMap_inclusion, D.reduces, Category.assoc, C.atPoint]

/-- The chart construction preserves the entire original first-jet map. -/
theorem deformation_inclusion {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map)) :
    (C.deformation D).map ≫ C.inclusion = D.map := C.familyMap_inclusion D

def velocity {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map)) :
    Y ⟶ AffineVelocity.tangentScheme C.evaluation :=
  velocityMorphism C.point C.point_overC (C.deformation D)

theorem velocity_overC {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map)) :
    C.velocity D ≫ AffineVelocity.tangentSchemeToC C.evaluation = sY :=
  velocityMorphism_overC C.point C.point_overC (C.deformation D)

/-- The regular functions of the actual chart velocity are the
coefficients of the factored original family. -/
theorem velocity_coordinate {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map)) (a : C.Ring) :
    (C.velocity D).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv
        (AffineVelocity.coordinate C.evaluation a)) =
      (C.deformation D).onFunction ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of C.Ring)).inv a) :=
  velocityMorphism_coordinate C.point C.point_overC (C.deformation D) a

/-- A function on an original target open containing the whole chart
has this particular affine coordinate, fixed by the canonical Gamma--Spec
comparison and the actual open-immersion pullback. -/
def localCoordinate (V : X.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V)
    (a : RingSections X.scheme V) : C.Ring :=
  (Scheme.ΓSpecIso (CommRingCat.of C.Ring)).hom (C.inclusion.appLE V ⊤ hV a)

theorem localCoordinate_function (V : X.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V)
    (a : RingSections X.scheme V) :
    (Scheme.ΓSpecIso (CommRingCat.of C.Ring)).inv (C.localCoordinate V hV a) =
      C.inclusion.appLE V ⊤ hV a :=
  Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of C.Ring)) _

/-- The central fixed-point map is supported in every open containing
this actual target chart. This derives the support premise used below. -/
theorem centre_preimage {Y : Scheme} (sY : Y ⟶ ComplexBase) (V : X.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V) :
    (⊤ : Y.Opens) ≤ (sY ≫ x.map) ⁻¹ᵁ V := by
  intro y _
  change x.map (sY y) ∈ V
  rw [← C.atPoint]
  exact hV (show C.point (sY y) ∈ (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) by trivial)

/-- The actual chart velocity on a local target function is the
coefficient of the original family, not a freely chosen coordinate model. -/
theorem velocity_original_localFunction {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map))
    (V : X.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V)
    (a : RingSections X.scheme V) :
    (C.velocity D).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv
        (AffineVelocity.coordinate C.evaluation (C.localCoordinate V hV a))) =
      localCoefficient D V (C.centre_preimage sY V hV) a := by
  rw [C.velocity_coordinate, C.localCoordinate_function, onFunction_top]
  have hm : C.inclusion.appLE V ⊤ hV ≫ (C.deformation D).map.appTop =
      D.map.appLE V ⊤ (family_preimage_top D V (C.centre_preimage sY V hV)) := by
    have ht : (C.deformation D).map.appTop =
        (C.deformation D).map.appLE ⊤ ⊤ le_rfl :=
      (C.deformation D).map.app_eq_appLE
    rw [ht, Scheme.Hom.appLE_comp_appLE]
    exact DualThickening.appLE_of_map_eq (C.deformation_inclusion D) V ⊤ _ _
  exact congrArg (DualThickening.coefficient sY ⊤)
    (congrArg (fun k => k a) hm)

/-- The same coordinate is normalized by the original variety's
universal differential. This is the local cotangent comparison needed
before identifying the represented target with the original tangent fiber. -/
theorem velocity_original_cotangent {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map))
    (V : X.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V)
    (a : RingSections X.scheme V) :
    (C.velocity D).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv
        (AffineVelocity.coordinate C.evaluation (C.localCoordinate V hV a))) =
      Y.presheaf.map (homOfLE (C.centre_preimage sY V hV)).op
        (D.cotangentHom.app ((sY ≫ x.map) ⁻¹ᵁ V)
          (pullLocalSection (sY ≫ x.map) (cotangentSheaf X.structureMap) V
            ((cotangentPresentation X.structureMap).differential.apply V a))) := by
  rw [C.velocity_original_localFunction, localCoefficient_cotangent]

/-- Factorization through an open immersion commutes with actual
parameter changes, proved by cancellation of that immersion. -/
theorem deformation_parameterChange {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map))
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    C.deformation (recenter (D.pullback g hg)
        (by rw [← Category.assoc, hg])) =
      parameterChange C.point (C.deformation D) g hg := by
  apply Deformation.ext
  apply (cancel_mono C.inclusion).mp
  rw [C.deformation_inclusion]
  change DualThickening.map g hg ≫ D.map =
    (DualThickening.map g hg ≫ (C.deformation D).map) ≫ C.inclusion
  rw [Category.assoc, C.deformation_inclusion]

theorem velocity_parameterChange {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (D : Deformation sY X.structureMap (sY ≫ x.map))
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    g ≫ C.velocity D =
      C.velocity (recenter (D.pullback g hg) (by rw [← Category.assoc, hg])) := by
  unfold velocity
  rw [C.deformation_parameterChange, velocityMorphism_parameterChange]

end TargetChart

/-- Build the affine chart with its actual induced C-algebra. The point
lift is supplied only by an open-immersion factorization. -/
def targetChartOfOpen (U : X.scheme.Opens) (hU : IsAffineOpen U)
    (hxU : Set.range x.map ⊆ (U : Set X.scheme)) : TargetChart X x := by
  letI : IsAffine U.toScheme := hU
  let sU : U.toScheme ⟶ ComplexBase := U.ι ≫ X.structureMap
  let q : ComplexBase ⟶ U.toScheme := IsOpenImmersion.lift U.ι x.map (by
    simpa only [Scheme.Opens.range_ι] using hxU)
  refine
    { Ring := SectionAlgebra.Functions sU ⊤
      commRing := inferInstance
      algebra := inferInstance
      inclusion := U.toScheme.isoSpec.inv ≫ U.ι
      openImmersion := inferInstance
      overC := ?_
      point := q ≫ U.toScheme.isoSpec.hom
      atPoint := ?_ }
  · calc
      (U.toScheme.isoSpec.inv ≫ U.ι) ≫ X.structureMap =
          U.toScheme.isoSpec.inv ≫ sU := Category.assoc _ _ _
      _ = U.toScheme.isoSpec.inv ≫
          (U.toScheme.toSpecΓ ≫
            DirectionCones.affineBaseMap (SectionAlgebra.Functions sU ⊤)) :=
          congrArg (fun k => U.toScheme.isoSpec.inv ≫ k) (toSpecΓ_overC sU).symm
      _ = DirectionCones.affineBaseMap (SectionAlgebra.Functions sU ⊤) := by
          rw [← Category.assoc, Scheme.isoSpec_inv_toSpecΓ, Category.id_comp]
  · rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact IsOpenImmersion.lift_fac _ _ _

/-- An affine target neighborhood exists at every specified complex
point. This uses mathlib's scheme affine-open basis, not a new admission. -/
theorem targetChart_exists : Nonempty (TargetChart X x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.scheme) (x := x.map (default : PrimeSpectrum ℂ))
    (U := ⊤) (show x.map (default : PrimeSpectrum ℂ) ∈ (⊤ : X.scheme.Opens) by trivial)
  refine ⟨targetChartOfOpen X x U hU ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim _ _
  change x.map z ∈ U
  rw [hz]
  exact hxU

/-- The normalization on local functions is available inside every
prescribed neighborhood of the fixed point, by the actual affine-open basis. -/
theorem targetChart_exists_inside (U : X.scheme.Opens)
    (hxU : Set.range x.map ⊆ (U : Set X.scheme)) :
    ∃ C : TargetChart X x,
      (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ U := by
  have hx : x.map (default : PrimeSpectrum ℂ) ∈ U := by
    apply hxU
    exact ⟨(default : PrimeSpectrum ℂ), rfl⟩
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.scheme) (x := x.map (default : PrimeSpectrum ℂ))
    (U := U) hx
  have hxV' : Set.range x.map ⊆ (V : Set X.scheme) := by
    rintro _ ⟨z, rfl⟩
    have hz : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim _ _
    change x.map z ∈ V
    rw [hz]
    exact hxV
  letI : IsAffine V.toScheme := hV
  refine ⟨targetChartOfOpen X x V hV hxV', ?_⟩
  intro z _
  change V.ι (V.toScheme.isoSpec.inv z) ∈ U
  exact hVU (V.toScheme.isoSpec.inv z).property

end ActualTargetCharts

section ActualHomVelocity

variable (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X) (x : ComplexPoint X)
variable (τ : HomFirstJet.SourceLift P p) (C : TargetChart X x)

/-- The actual velocity morphism of the full fixed-node Hom family,
constructed from its source first jet and one actual affine target chart. -/
def homVelocity : FixedNodeHom.parameter P p H x ⟶
    AffineVelocity.tangentScheme C.evaluation :=
  C.velocity (HomFirstJet.deformation P p H x τ)

theorem homVelocity_overC :
    homVelocity P p H x τ C ≫ AffineVelocity.tangentSchemeToC C.evaluation =
      FixedNodeHom.toC P p H x :=
  C.velocity_overC (HomFirstJet.deformation P p H x τ)

/-- All regular coordinate functions of this morphism come from the
actual restricted universal evaluation map. -/
theorem homVelocity_coordinate (a : C.Ring) :
    (homVelocity P p H x τ C).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv
        (AffineVelocity.coordinate C.evaluation a)) =
      (C.deformation (HomFirstJet.deformation P p H x τ)).onFunction ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of C.Ring)).inv a) :=
  C.velocity_coordinate (HomFirstJet.deformation P p H x τ) a

/-- This chart factorization has the exact source-first-jet family as
its composite into the original target variety. -/
theorem homVelocity_family_inclusion :
    (C.deformation (HomFirstJet.deformation P p H x τ)).map ≫ C.inclusion =
      HomFirstJet.sourceMap P p (FixedNodeHom.toC P p H x) τ ≫
        FixedNodeHom.evaluation P p H x :=
  C.deformation_inclusion (HomFirstJet.deformation P p H x τ)

/-- The global scheme morphism and the existing regular section of the
ORIGINAL pulled-back tangent sheaf have the same normalized action on
every original local target differential whose domain contains the chart.
No arbitrary identification of tangent fibers appears in the statement. -/
theorem homVelocity_original_section
    (V : X.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V)
    (a : RingSections X.scheme V) :
    (homVelocity P p H x τ C).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv
        (AffineVelocity.coordinate C.evaluation (C.localCoordinate V hV a))) =
      (FixedNodeHom.parameter P p H x).presheaf.map
        (homOfLE (C.centre_preimage (FixedNodeHom.toC P p H x) V hV)).op
        ((TwoChartSections.internalHomSectionAddEquiv _ _
          (sectionFromValue (HomFirstJet.velocitySection P p H x τ) ≫
            dualBaseChange (FixedNodeHom.toC P p H x ≫ x.map)
              (cotangentSheaf X.structureMap))).app
          ((FixedNodeHom.toC P p H x ≫ x.map) ⁻¹ᵁ V)
          (pullLocalSection (FixedNodeHom.toC P p H x ≫ x.map)
            (cotangentSheaf X.structureMap) V
            ((cotangentPresentation X.structureMap).differential.apply V a))) := by
  rw [HomFirstJet.velocitySection_normalized]
  exact C.velocity_original_cotangent (HomFirstJet.deformation P p H x τ) V hV a

/-- Restriction to any family parameter, including nonreduced ones,
commutes with the globally constructed velocity map. -/
theorem homVelocity_parameterChange {T : Scheme} {sT : T ⟶ ComplexBase}
    (g : PointsOver T sT (FixedNodeHom.parameter P p H x)
      (FixedNodeHom.toC P p H x)) :
    g.val ≫ homVelocity P p H x τ C =
      C.velocity (recenter
        ((HomFirstJet.deformation P p H x τ).pullback g.val g.property)
        (by rw [← Category.assoc, g.property])) :=
  C.velocity_parameterChange (HomFirstJet.deformation P p H x τ) g.val g.property

end ActualHomVelocity

end LeBrunSalamon.Construction.Lines.GlobalVelocity

end

/-!
## Differentiating the actual positive section at its zero

The chart and the scalar coordinate below refer to the existing marked
point. No identification of that point with the explicit coordinate zero
is used. The actual twist frames, actual coproduct maps and actual
free-line splitting give the coefficient and fiber comparisons.

At a zero of a section, the first derivative commutes with actual bundle
maps: the differentiated matrix contributes zero. The resulting derivative
of the already constructed fixed-node Hom variation belongs to the
original positive node space. Equality with the differential of the
global velocity morphism is a separate mixed-jet comparison.

This continuation has no new admitted input. Compilation is deferred to
the user-requested 45,000-line gate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open scoped BigOperators Classical

namespace LeBrunSalamon.Construction.Lines.PositiveFrame

/-! ### Fiber functor calculations for the actual finite coproduct -/

@[simp]
theorem fiberMap_id {Y : Scheme} (E : OModule Y) (x : ComplexBase ⟶ Y)
    (v : Fiber E x) : fiberMap (𝟙 E) x v = v := by
  change ((Scheme.Modules.pullback x).map (𝟙 E)).app ⊤ v = v
  rw [CategoryTheory.Functor.map_id] <;> rfl

@[simp]
theorem fiberMap_zero {Y : Scheme} (E F : OModule Y) (x : ComplexBase ⟶ Y)
    (v : Fiber E x) : fiberMap (0 : E ⟶ F) x v = 0 := by
  change ((Scheme.Modules.pullback x).map (0 : E ⟶ F)).app ⊤ v = 0
  rw [Functor.map_zero]
  rfl

theorem fiberMap_sum {Y : Scheme} {E F : OModule Y} (x : ComplexBase ⟶ Y)
    {J : Type} (s : Finset J) (a : J → (E ⟶ F)) (v : Fiber E x) :
    fiberMap (∑ j ∈ s, a j) x v = ∑ j ∈ s, fiberMap (a j) x v := by
  change ((Scheme.Modules.pullback x).map (∑ j ∈ s, a j)).app ⊤ v = _
  rw [Functor.map_sum]
  have h := DirectSumSections.onCSections_sum (𝟙 ComplexBase) s
    (fun j => (Scheme.Modules.pullback x).map (a j))
  change onCSections (𝟙 ComplexBase)
    (∑ j ∈ s, (Scheme.Modules.pullback x).map (a j)) v = _
  simpa only [LinearMap.sum_apply, fiberMap] using congrArg (fun k => k v) h

theorem fiberCoproduct_total {Y : Scheme} {I : Type} [Fintype I]
    (E : I → OModule Y) (x : ComplexBase ⟶ Y) (v : Fiber (∐ E) x) :
    (∑ j, fiberMap (Sigma.ι E j) x (fiberMap (Sigma.π E j) x v)) = v := by
  classical
  have h := congrArg (fun k : (∐ E) ⟶ ∐ E => fiberMap k x v)
    (DirectSumGeometry.coproduct_total E)
  rw [fiberMap_sum, fiberMap_id] at h
  simpa only [ContactPositive.fiberMap_comp] using h

/-- Fiber coordinates use the actual pulled-back coproduct projections.
The inverse uses its actual inclusions, not an unrelated vector-space iso. -/
def fiberCoproductEquiv {Y : Scheme} {I : Type} [Fintype I]
    (E : I → OModule Y) (x : ComplexBase ⟶ Y) :
    Fiber (∐ E) x ≃ₗ[ℂ] (∀ j, Fiber (E j) x) := by
  classical
  exact
    { toFun := fun v j => fiberMap (Sigma.π E j) x v
      invFun := fun v => ∑ j, fiberMap (Sigma.ι E j) x (v j)
      left_inv := fiberCoproduct_total E x
      right_inv := by
        intro v
        funext k
        change fiberMap (Sigma.π E k) x
          (∑ j, fiberMap (Sigma.ι E j) x (v j)) = v k
        rw [map_sum, Finset.sum_eq_single k]
        · rw [← ContactPositive.fiberMap_comp, Sigma.ι_π_eq_id, fiberMap_id]
        · intro j _ hjk
          rw [← ContactPositive.fiberMap_comp, Sigma.ι_π_of_ne E hjk,
            fiberMap_zero]
        · simp
      map_add' := by
        intro u v
        funext j
        exact map_add (fiberMap (Sigma.π E j) x) u v
      map_smul' := by
        intro c v
        funext j
        exact map_smul (fiberMap (Sigma.π E j) x) c v }

theorem fiberCoproduct_ext {Y : Scheme} {I : Type} [Fintype I]
    (E : I → OModule Y) (x : ComplexBase ⟶ Y)
    {v w : Fiber (∐ E) x}
    (h : ∀ j, fiberMap (Sigma.π E j) x v = fiberMap (Sigma.π E j) x w) : v = w := by
  apply (fiberCoproductEquiv E x).injective
  funext j
  exact h j

/-! ### Normalized chart coefficients of the original twists -/

/-- Restriction followed by the actual twist-frame coordinate. The scalar
structure on sections is the canonical complex structure of the source. -/
def twistCoefficient (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (d : ℤ) (i : Fin 2) :
    CSections P.structureMap (projectiveTwist Q p d).sheaf →ₗ[ℂ] Polynomial ℂ where
  toFun s := polynomialCoordinates Q p d i
    (TwoChartSections.restrictValue (projectiveTwist Q p d).sheaf le_top s)
  map_add' s t := by
    rw [TwoChartSections.restrictValue, map_add, map_add]
  map_smul' c s :=
    P1TwistSections.polynomialCoordinates_restrict_canonical_smul Q p d i c s

/-- The fiber frame is pulled back through the actual factorization of the
specified point into its chart. Its coordinate need not be zero. -/
def twistNodeFrame (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (d : ℤ) (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x) :
    structureModule ComplexBase ≅ pullbackModule x (projectiveTwist Q p d).sheaf :=
  FrameEvaluation.fiberFrame (chartOpen i) (P1TwistEvaluation.pointInOpen i c) x
    ((P1TwistEvaluation.pointInOpen_ι i c).trans hchart) (twistOverFrame Q p d i)

def twistFiberCoordinates (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (d : ℤ) (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x) :
    Fiber (projectiveTwist Q p d).sheaf x ≃ₗ[ℂ] ℂ :=
  FrameEvaluation.complexFrameCoordinatesLinearEquiv
    (twistNodeFrame Q p d x i c hchart)

/-- The actual fiber coordinate of a global section is its actual chart
coefficient evaluated at the genuine coordinate of the point. -/
theorem twistCoefficient_value (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (d : ℤ) (x : ComplexBase ⟶ ProjectiveLine)
    (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (s : CSections P.structureMap (projectiveTwist Q p d).sheaf) :
    twistFiberCoordinates Q p d x i c hchart
        (evaluateSection P.structureMap (projectiveTwist Q p d).sheaf x hx s) =
      (Polynomial.aeval c) (twistCoefficient Q p d i s) := by
  have h := FrameEvaluation.complexFiberFrameCoordinates_pullSection
    (chartOpen i) (P1TwistEvaluation.pointInOpen i c) x
    ((P1TwistEvaluation.pointInOpen_ι i c).trans hchart)
    (twistOverFrame Q p d i) (polynomialChartRingEquiv i)
    (Polynomial.eval c) (P1TwistEvaluation.pointInOpen_ring_value i c)
    (sectionFromValue s)
  change FrameEvaluation.complexFrameCoordinates
      (twistNodeFrame Q p d x i c hchart)
      (sectionValue (pullSection x (sectionFromValue s))) =
    (Polynomial.aeval c) (twistCoefficient Q p d i s)
  rw [sectionFromValue_spec] at h
  exact h

theorem twistCoefficient_value_zero (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint Q) (d : ℤ) (x : ComplexBase ⟶ ProjectiveLine)
    (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (s : CSections P.structureMap (projectiveTwist Q p d).sheaf)
    (hs : evaluateSection P.structureMap (projectiveTwist Q p d).sheaf x hx s = 0) :
    (Polynomial.aeval c) (twistCoefficient Q p d i s) = 0 := by
  rw [← twistCoefficient_value Q p d x hx i c hchart s, hs, map_zero]

/-- For nonnegative twists the frame on either complete standard chart
extends to an actual global section. This is the explicit pair of monomial
sections already constructed by genuine sheaf gluing. -/
theorem chartGenerator_exists (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (d : ℤ) (hd : 0 ≤ d) (i : Fin 2) :
    ∃ s : CSections P.structureMap (projectiveTwist Q p d).sheaf,
      TwoChartSections.restrictValue (projectiveTwist Q p d).sheaf le_top s =
        LocalFrames.generator (twistOverFrame Q p d i) := by
  lift d to ℕ using hd
  fin_cases i
  · refine ⟨sectionValue (P1TwistGeneration.zeroGeneratorSection Q p d), ?_⟩
    exact (ScalarSections.section_app_one
      (P1TwistGeneration.zeroGeneratorSection Q p d) (chartOpen 0)).symm.trans
        (P1TwistGeneration.zeroGeneratorSection_app_one Q p d)
  · refine ⟨sectionValue (P1TwistGeneration.oneGeneratorSection Q p d), ?_⟩
    exact (ScalarSections.section_app_one
      (P1TwistGeneration.oneGeneratorSection Q p d) (chartOpen 1)).symm.trans
        (P1TwistGeneration.oneGeneratorSection_app_one Q p d)

def chartGenerator (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (d : ℤ) (hd : 0 ≤ d) (i : Fin 2) :
    CSections P.structureMap (projectiveTwist Q p d).sheaf :=
  Classical.choose (chartGenerator_exists Q p d hd i)

theorem chartGenerator_restrict (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint Q) (d : ℤ) (hd : 0 ≤ d) (i : Fin 2) :
    TwoChartSections.restrictValue (projectiveTwist Q p d).sheaf le_top
        (chartGenerator Q p d hd i) = LocalFrames.generator (twistOverFrame Q p d i) :=
  Classical.choose_spec (chartGenerator_exists Q p d hd i)

@[simp]
theorem chartGenerator_coefficient (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint Q) (d : ℤ) (hd : 0 ≤ d) (i : Fin 2) :
    twistCoefficient Q p d i (chartGenerator Q p d hd i) = 1 := by
  change polynomialCoordinates Q p d i _ = 1
  rw [chartGenerator_restrict, polynomialCoordinates_generator]

theorem chartGenerator_fiber (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (d : ℤ) (hd : 0 ≤ d) (x : ComplexBase ⟶ ProjectiveLine)
    (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x) :
    evaluateSection P.structureMap (projectiveTwist Q p d).sheaf x hx
        (chartGenerator Q p d hd i) =
      (twistFiberCoordinates Q p d x i c hchart).symm 1 := by
  apply (twistFiberCoordinates Q p d x i c hchart).injective
  rw [twistCoefficient_value, chartGenerator_coefficient, map_one,
    LinearEquiv.apply_symm_apply]

/-! ### The genuine moving-coefficient calculation for a sheaf map -/

/-- This is the coefficient of the actual sheaf map in two actual local
frames. It may vary along the source and is not treated as a constant. -/
def twistMapCoefficient (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (R : ProjectiveLineOverC) (q : ProjectiveLinePoint R)
    (a b : ℤ) (i : Fin 2)
    (h : (projectiveTwist Q p a).sheaf ⟶ (projectiveTwist R q b).sheaf) :
    Polynomial ℂ :=
  polynomialChartRingEquiv i
    (LocalFrames.mapCoefficient (twistOverFrame Q p a i) (twistOverFrame R q b i) h)

theorem twistCoefficient_map (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (R : ProjectiveLineOverC) (q : ProjectiveLinePoint R)
    (a b : ℤ) (i : Fin 2)
    (h : (projectiveTwist Q p a).sheaf ⟶ (projectiveTwist R q b).sheaf)
    (s : CSections P.structureMap (projectiveTwist Q p a).sheaf) :
    twistCoefficient R q b i (onCSections P.structureMap h s) =
      twistCoefficient Q p a i s * twistMapCoefficient Q p R q a b i h := by
  unfold twistCoefficient
  have hn := sheafHom_naturality h (homOfLE (show chartOpen i ≤ ⊤ from le_top)) s
  change (projectiveTwist R q b).sheaf.presheaf.map (homOfLE le_top).op
      (h.app ⊤ s) =
    h.app (chartOpen i)
      ((projectiveTwist Q p a).sheaf.presheaf.map (homOfLE le_top).op s) at hn
  change polynomialCoordinates R q b i
      ((projectiveTwist R q b).sheaf.presheaf.map (homOfLE le_top).op (h.app ⊤ s)) = _
  rw [hn]
  change polynomialChartRingEquiv i
      (LocalFrames.coordinates (twistOverFrame R q b i)
        (h.app (chartOpen i) _)) = _
  rw [LocalFrames.map_coordinates, map_mul]
  rfl

/-- An actual map on the actual fibers has the evaluated frame-matrix
entry. The source's nonnegative degree is used only to obtain a genuine
global section equal to its chart frame; its fiber value is proved above. -/
theorem twistFiberCoordinates_map
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (R : ProjectiveLineOverC) (q : ProjectiveLinePoint R)
    (a b : ℤ) (ha : 0 ≤ a)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (h : (projectiveTwist Q p a).sheaf ⟶ (projectiveTwist R q b).sheaf)
    (v : Fiber (projectiveTwist Q p a).sheaf x) :
    twistFiberCoordinates R q b x i c hchart (fiberMap h x v) =
      twistFiberCoordinates Q p a x i c hchart v *
        (Polynomial.aeval c) (twistMapCoefficient Q p R q a b i h) := by
  let e := twistFiberCoordinates Q p a x i c hchart
  let g := chartGenerator Q p a ha i
  have hv : v = e v • evaluateSection P.structureMap
      (projectiveTwist Q p a).sheaf x hx g := by
    apply e.injective
    rw [map_smul]
    have hg : e (evaluateSection P.structureMap
        (projectiveTwist Q p a).sheaf x hx g) = 1 := by
      dsimp [e, g]
      rw [twistCoefficient_value, chartGenerator_coefficient, map_one]
    rw [hg, smul_eq_mul, mul_one]
  nth_rewrite 1 [hv]
  rw [map_smul, map_smul, ← PositiveQuotient.evaluateSection_naturality,
    twistCoefficient_value, twistCoefficient_map, chartGenerator_coefficient,
    one_mul] <;> rfl

def twistDerivative (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (d : ℤ) (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c)) :
    CSections P.structureMap (projectiveTwist Q p d).sheaf →ₗ[ℂ]
      Fiber (projectiveTwist Q p d).sheaf x :=
  (twistFiberCoordinates Q p d x i c hchart).symm.toLinearMap.comp
    (D.val.comp (twistCoefficient Q p d i))

@[simp]
theorem twistDerivative_coordinates (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint Q) (d : ℤ) (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (s : CSections P.structureMap (projectiveTwist Q p d).sheaf) :
    twistFiberCoordinates Q p d x i c hchart
        (twistDerivative Q p d x i c hchart D s) =
      D.val (twistCoefficient Q p d i s) :=
  (twistFiberCoordinates Q p d x i c hchart).apply_symm_apply _

/-- The moving-frame term is cancelled by the proved value-zero premise.
The conclusion compares the actual sheaf map and its actual fiber map. -/
theorem twistDerivative_naturality
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (R : ProjectiveLineOverC) (q : ProjectiveLinePoint R)
    (a b : ℤ) (ha : 0 ≤ a)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (h : (projectiveTwist Q p a).sheaf ⟶ (projectiveTwist R q b).sheaf)
    (s : CSections P.structureMap (projectiveTwist Q p a).sheaf)
    (hs : evaluateSection P.structureMap (projectiveTwist Q p a).sheaf x hx s = 0) :
    twistDerivative R q b x i c hchart D (onCSections P.structureMap h s) =
      fiberMap h x (twistDerivative Q p a x i c hchart D s) := by
  apply (twistFiberCoordinates R q b x i c hchart).injective
  rw [twistDerivative_coordinates, twistCoefficient_map, D.property,
    twistCoefficient_value_zero Q p a x hx i c hchart s hs,
    zero_mul, zero_add,
    twistFiberCoordinates_map Q p R q a b ha x hx i c hchart,
    twistDerivative_coordinates]
  exact mul_comm _ _

/-! ### Finite actual sums and a genuine splitting of an ambient bundle -/

abbrev twistFamily (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} (d : I → ℤ) : I → OModule ProjectiveLine :=
  fun j => (projectiveTwist Q p (d j)).sheaf

def sumCoefficient (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (d : I → ℤ) (i : Fin 2)
    (s : CSections P.structureMap (∐ twistFamily Q p d)) (j : I) : Polynomial ℂ :=
  twistCoefficient Q p (d j) i
    (onCSections P.structureMap (Sigma.π (twistFamily Q p d) j) s)

theorem sumCoefficient_value_zero (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint Q) {I : Type} [Fintype I] (d : I → ℤ)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (s : CSections P.structureMap (∐ twistFamily Q p d))
    (hs : evaluateSection P.structureMap (∐ twistFamily Q p d) x hx s = 0)
    (j : I) : (Polynomial.aeval c) (sumCoefficient Q p d i s j) = 0 := by
  apply twistCoefficient_value_zero Q p (d j) x hx i c hchart
  rw [PositiveQuotient.evaluateSection_naturality, hs, map_zero]

/-- Differentiate each actual twist coordinate and include its value by
the actual fiber map. This is a linear map on genuine global sections. -/
def sumDerivative (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (d : I → ℤ)
    (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c)) :
    CSections P.structureMap (∐ twistFamily Q p d) →ₗ[ℂ]
      Fiber (∐ twistFamily Q p d) x :=
  ∑ j, (fiberMap (Sigma.ι (twistFamily Q p d) j) x).comp
    ((twistDerivative Q p (d j) x i c hchart D).comp
      (onCSections P.structureMap (Sigma.π (twistFamily Q p d) j)))

theorem sumDerivative_projection (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint Q) {I : Type} [Fintype I] (d : I → ℤ)
    (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (s : CSections P.structureMap (∐ twistFamily Q p d)) (j : I) :
    fiberMap (Sigma.π (twistFamily Q p d) j) x
        (sumDerivative Q p d x i c hchart D s) =
      twistDerivative Q p (d j) x i c hchart D
        (onCSections P.structureMap (Sigma.π (twistFamily Q p d) j) s) := by
  classical
  simp only [sumDerivative, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  rw [Finset.sum_eq_single j]
  · rw [← ContactPositive.fiberMap_comp, Sigma.ι_π_eq_id, fiberMap_id] <;> rfl
  · intro k _ hkj
    rw [← ContactPositive.fiberMap_comp, Sigma.ι_π_of_ne _ hkj, fiberMap_zero]
  · simp

/-- Projecting the source section and then evaluating really yields zero;
coefficient vanishing is derived from that statement, not supplied data. -/
theorem projection_node_zero {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {I : Type} [Fintype I] (E : I → OModule Y)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (s : CSections sY (∐ E)) (hs : evaluateSection sY (∐ E) x hx s = 0)
    (j : I) :
    evaluateSection sY (E j) x hx (onCSections sY (Sigma.π E j) s) = 0 := by
  rw [PositiveQuotient.evaluateSection_naturality, hs, map_zero]

/-- Every target component of an actual map out of the finite sum is
computed from its actual source components. -/
theorem section_map_coproduct {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {I : Type} [Fintype I] (E : I → OModule Y) {F : OModule Y}
    (h : (∐ E) ⟶ F) (s : CSections sY (∐ E)) :
    onCSections sY h s =
      ∑ j, onCSections sY (Sigma.ι E j ≫ h)
        (onCSections sY (Sigma.π E j) s) := by
  have hs := (DirectSumSections.cSectionsCoproductEquiv sY E).left_inv s
  change (∑ j, onCSections sY (Sigma.ι E j)
    (onCSections sY (Sigma.π E j) s)) = s at hs
  conv_lhs => rw [← hs]
  rw [map_sum]
  rfl

/-- Naturality of the vanishing-section derivative for an actual map of
finite sums. Source nonnegativity provides normalized genuine frame
sections; no matrix comparison or fiber-membership assumption is present. -/
theorem sumDerivative_naturality
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (R : ProjectiveLineOverC) (q : ProjectiveLinePoint R)
    {I J : Type} [Fintype I] [Fintype J] (a : I → ℤ) (b : J → ℤ)
    (ha : ∀ j, 0 ≤ a j)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (h : (∐ twistFamily Q p a) ⟶ ∐ twistFamily R q b)
    (s : CSections P.structureMap (∐ twistFamily Q p a))
    (hs : evaluateSection P.structureMap (∐ twistFamily Q p a) x hx s = 0) :
    sumDerivative R q b x i c hchart D (onCSections P.structureMap h s) =
      fiberMap h x (sumDerivative Q p a x i c hchart D s) := by
  apply fiberCoproduct_ext (twistFamily R q b) x
  intro k
  rw [sumDerivative_projection]
  change twistDerivative R q (b k) x i c hchart D
      (onCSections P.structureMap (h ≫ Sigma.π (twistFamily R q b) k) s) = _
  rw [section_map_coproduct, map_sum]
  simp only [sumDerivative, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [ContactPositive.fiberMap_comp, LinearMap.comp_apply] using
    twistDerivative_naturality Q p R q (a j) (b k) (ha j) x hx i c hchart D
    (Sigma.ι (twistFamily Q p a) j ≫ h ≫ Sigma.π (twistFamily R q b) k)
    (onCSections P.structureMap (Sigma.π (twistFamily Q p a) j) s)
    (projection_node_zero P.structureMap (twistFamily Q p a) x hx s hs j)

/-- A derivative in a genuine splitting of the original bundle. Only the
actual sheaf isomorphism transports the coordinate derivative. -/
def realizedDerivative {E : OModule ProjectiveLine}
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ) (e : E ≅ ∐ twistFamily Q p a)
    (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c)) :
    CSections P.structureMap E →ₗ[ℂ] Fiber E x :=
  (fiberMap e.inv x).comp
    ((sumDerivative Q p a x i c hchart D).comp
      (onCSections P.structureMap e.hom))

theorem realizedDerivative_naturality
    {E F : OModule ProjectiveLine}
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (R : ProjectiveLineOverC) (q : ProjectiveLinePoint R)
    {I J : Type} [Fintype I] [Fintype J] (a : I → ℤ) (b : J → ℤ)
    (ha : ∀ j, 0 ≤ a j)
    (e : E ≅ ∐ twistFamily Q p a) (f : F ≅ ∐ twistFamily R q b)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (h : E ⟶ F) (s : CSections P.structureMap E)
    (hs : evaluateSection P.structureMap E x hx s = 0) :
    realizedDerivative R q b f x i c hchart D (onCSections P.structureMap h s) =
      fiberMap h x (realizedDerivative Q p a e x i c hchart D s) := by
  have hz : evaluateSection P.structureMap (∐ twistFamily Q p a) x hx
      (onCSections P.structureMap e.hom s) = 0 := by
    rw [PositiveQuotient.evaluateSection_naturality, hs, map_zero]
  have hn := sumDerivative_naturality Q p R q a b ha x hx i c hchart D
    (e.inv ≫ h ≫ f.hom) (onCSections P.structureMap e.hom s) hz
  have hsec : onCSections P.structureMap (e.inv ≫ h ≫ f.hom)
      (onCSections P.structureMap e.hom s) =
      onCSections P.structureMap f.hom (onCSections P.structureMap h s) := by
    change onCSections P.structureMap (e.hom ≫ e.inv ≫ h ≫ f.hom) s = _
    rw [Iso.hom_inv_id_assoc]
    rfl
  rw [hsec] at hn
  change fiberMap f.inv x
      (sumDerivative R q b x i c hchart D
        (onCSections P.structureMap f.hom (onCSections P.structureMap h s))) = _
  rw [hn, ← ContactPositive.fiberMap_comp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [ContactPositive.fiberMap_comp]
  rfl

/-- On a section vanishing at the point, two nonnegative splittings of
the same actual bundle yield the same first derivative in its actual
fiber. This is not merely independence of an abstract coordinate dimension. -/
theorem realizedDerivative_independent_splitting
    {E : OModule ProjectiveLine}
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    (R : ProjectiveLineOverC) (q : ProjectiveLinePoint R)
    {I J : Type} [Fintype I] [Fintype J] (a : I → ℤ) (b : J → ℤ)
    (ha : ∀ j, 0 ≤ a j)
    (e : E ≅ ∐ twistFamily Q p a) (f : E ≅ ∐ twistFamily R q b)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (s : CSections P.structureMap E)
    (hs : evaluateSection P.structureMap E x hx s = 0) :
    realizedDerivative R q b f x i c hchart D s =
      realizedDerivative Q p a e x i c hchart D s := by
  simpa only [DirectSumSections.onCSections_id, LinearMap.id_apply, fiberMap_id] using
    realizedDerivative_naturality Q p R q a b ha e f x hx i c hchart D (𝟙 E) s hs

/-! ### Specialization to the actual free-line positive lift -/

def positiveDerivative {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c)) :
    CSections P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf →ₗ[ℂ]
      Fiber (PositivePart.freeLinePositiveBundle f).sheaf marking.map :=
  sumDerivative P marking (fun j : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
    (PositivePart.freeLineProfile f).degree j.val) marking.map i c hchart D

def ambientDerivative {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c)) :
    CSections P.structureMap (PositivePart.freeLineBundle f).sheaf →ₗ[ℂ]
      Fiber (PositivePart.freeLineBundle f).sheaf marking.map :=
  realizedDerivative P marking (PositivePart.freeLineProfile f).degree
    (PositivePart.freeLineSplitting f) marking.map i c hchart D

/-- The derivative of the included positive section is the actual fiber
inclusion of its derivative. The section's value-zero equation kills the
moving ambient frame term in the preceding naturality proof. -/
theorem positiveDerivative_inclusion {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (s : CSections P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf)
    (hs : evaluateSection P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf
      marking.map marking.overC s = 0) :
    ambientDerivative f i c hchart D
        (onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f) s) =
      fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map
        (positiveDerivative f i c hchart D s) := by
  let a := fun j : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
    (PositivePart.freeLineProfile f).degree j.val
  have hn := realizedDerivative_naturality P marking P marking a
    (PositivePart.freeLineProfile f).degree (fun j => le_of_lt j.property)
    (Iso.refl (PositivePart.freeLinePositiveBundle f).sheaf)
    (PositivePart.freeLineSplitting f) marking.map marking.overC i c hchart D
    (PositivePart.freeLinePositiveInclusion f) s hs
  change ambientDerivative f i c hchart D
      (onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f) s) =
    fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map
      (fiberMap (𝟙 (PositivePart.freeLinePositiveBundle f).sheaf) marking.map
        (positiveDerivative f i c hchart D s)) at hn
  rw [fiberMap_id] at hn
  exact hn

def nodeSectionDerivative {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c)) :
    CSections P.structureMap (PositivePart.freeLineBundle f).sheaf →ₗ[ℂ]
      TangentFiber X.variety x :=
  (fiberComposition f.curve.map marking.map x.map hx
    (tangentSheaf X.variety.structureMap)).comp (ambientDerivative f i c hchart D)

theorem nodeSectionDerivative_positive_mem {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (s : CSections P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf)
    (hs : evaluateSection P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf
      marking.map marking.overC s = 0) :
    nodeSectionDerivative f x hx i c hchart D
        (onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f) s) ∈
      positiveNodeSpace f x hx := by
  rw [PositiveNodeImage.freeLine_positiveNodeSpace_eq_fiberImage f x hx]
  refine LinearMap.mem_range.mpr ⟨positiveDerivative f i c hchart D s, ?_⟩
  change fiberComposition f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)
        (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map
          (positiveDerivative f i c hchart D s)) = _
  rw [← positiveDerivative_inclusion f i c hchart D s hs]
  rfl

/-- The actual family produces the section and its zero; the positive
coefficient vanishing required by the derivative calculation is a result. -/
theorem fixedLinePositiveVariation_coefficients_vanish
    {n : ℕ} {X : ContactFanoManifold n}
    (H : HomSpacePresentation P X.variety) (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (v : HomDeformation.FixedLineLift H f x hx)
    (j : PositivePart.PositiveIndex (PositivePart.freeLineProfile f)) :
    (Polynomial.aeval c)
      (sumCoefficient P marking
        (fun k : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
          (PositivePart.freeLineProfile f).degree k.val) i
        (HomDeformation.fixedLinePositiveVariation H f x hx v) j) = 0 :=
  sumCoefficient_value_zero P marking _ marking.map marking.overC i c hchart
    (HomDeformation.fixedLinePositiveVariation H f x hx v)
    (HomDeformation.fixedLinePositiveVariation_node_zero H f x hx v) j

/-- The actual infinitesimal Hom parameter yields a derivative in the
original positive node space. This is the source derivative of the actual
variation section; identifying it with the parameter derivative of velocity
still requires the actual mixed-jet comparison. -/
theorem fixedLineVariation_derivative_mem
    {n : ℕ} {X : ContactFanoManifold n}
    (H : HomSpacePresentation P X.variety) (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (v : HomDeformation.FixedLineLift H f x hx) :
    nodeSectionDerivative f x hx i c hchart D
        (HomDeformation.fixedLineVariation H f x hx v) ∈ positiveNodeSpace f x hx := by
  rw [← HomDeformation.fixedLinePositiveVariation_inclusion H f x hx v]
  exact nodeSectionDerivative_positive_mem f x hx i c hchart D
    (HomDeformation.fixedLinePositiveVariation H f x hx v)
    (HomDeformation.fixedLinePositiveVariation_node_zero H f x hx v)

/-! ### The actual positive frame and its original image -/

/-- Actual normalized coordinates on the pulled-back finite twist sum. -/
def sumFiberCoordinates (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ)
    (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x) :
    Fiber (∐ twistFamily Q p a) x ≃ₗ[ℂ] (I → ℂ) :=
  (fiberCoproductEquiv (twistFamily Q p a) x).trans
    (LinearEquiv.piCongrRight (fun j => twistFiberCoordinates Q p (a j) x i c hchart))

theorem sumFiberCoordinates_derivative (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint Q) {I : Type} [Fintype I] (a : I → ℤ)
    (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (s : CSections P.structureMap (∐ twistFamily Q p a)) :
    sumFiberCoordinates Q p a x i c hchart
        (sumDerivative Q p a x i c hchart D s) =
      fun j => D.val (sumCoefficient Q p a i s j) := by
  funext j
  change twistFiberCoordinates Q p (a j) x i c hchart
    (fiberMap (Sigma.π (twistFamily Q p a) j) x
      (sumDerivative Q p a x i c hchart D s)) = _
  rw [sumDerivative_projection, twistDerivative_coordinates]
  rfl

/-- The positive-fiber inclusion has a proved left inverse, inherited
from the actual categorical splitting. Fiber injectivity here needs no
separate exactness-of-pullback admission. -/
theorem positiveFiberInclusion_injective {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) :
    Function.Injective (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map) := by
  let r := PositivePart.positiveRetraction P marking
    (PositivePart.freeLineProfile f) (PositivePart.freeLineSplitting f)
  have hr : PositivePart.freeLinePositiveInclusion f ≫ r = 𝟙 _ :=
    PositivePart.positive_retraction P marking
      (PositivePart.freeLineProfile f) (PositivePart.freeLineSplitting f)
  have hl : Function.LeftInverse (fiberMap r marking.map)
      (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map) := by
    intro u
    rw [← ContactPositive.fiberMap_comp, hr]
    exact fiberMap_id (PositivePart.freeLinePositiveBundle f).sheaf marking.map u
  exact hl.injective

def positiveFiberCoordinates {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map) :
    Fiber (PositivePart.freeLinePositiveBundle f).sheaf marking.map ≃ₗ[ℂ]
      (PositivePart.PositiveIndex (PositivePart.freeLineProfile f) → ℂ) :=
  sumFiberCoordinates P marking
    (fun j : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
      (PositivePart.freeLineProfile f).degree j.val) marking.map i c hchart

/-- This map is made from the actual local positive frame, the actual
positive inclusion, and the original composition-pullback comparison.
Its range is proved to be the original positive node space below. -/
def positiveNodeFrameMap {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map) :
    (PositivePart.PositiveIndex (PositivePart.freeLineProfile f) → ℂ) →ₗ[ℂ]
      TangentFiber X.variety x :=
  (fiberComposition f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)).comp
    ((fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map).comp
      (positiveFiberCoordinates f i c hchart).symm.toLinearMap)

theorem positiveNodeFrameMap_injective {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map) :
    Function.Injective (positiveNodeFrameMap f x hx i c hchart) :=
  (fiberComposition_bijective f.curve.map marking.map x.map hx
    (tangentSheaf X.variety.structureMap)).1.comp
      ((positiveFiberInclusion_injective f).comp
        (positiveFiberCoordinates f i c hchart).symm.injective)

theorem positiveNodeFrameMap_range {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map) :
    LinearMap.range (positiveNodeFrameMap f x hx i c hchart) = positiveNodeSpace f x hx := by
  rw [PositiveNodeImage.freeLine_positiveNodeSpace_eq_fiberImage f x hx]
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(positiveFiberCoordinates f i c hchart).symm a, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨positiveFiberCoordinates f i c hchart w, ?_⟩
    change fiberComposition f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)
      (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map
        ((positiveFiberCoordinates f i c hchart).symm
          (positiveFiberCoordinates f i c hchart w))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

theorem positiveNodeFrameMap_mem {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (a : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) → ℂ) :
    positiveNodeFrameMap f x hx i c hchart a ∈ positiveNodeSpace f x hx := by
  rw [← positiveNodeFrameMap_range f x hx i c hchart]
  exact ⟨a, rfl⟩

/-- The surviving coefficient derivatives, in the actual positive frame,
are exactly the original ambient derivative of the included section. -/
theorem nodeSectionDerivative_positive_formula
    {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (s : CSections P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf)
    (hs : evaluateSection P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf
      marking.map marking.overC s = 0) :
    nodeSectionDerivative f x hx i c hchart D
        (onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f) s) =
      positiveNodeFrameMap f x hx i c hchart
        (fun j => D.val (sumCoefficient P marking
          (fun k : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
            (PositivePart.freeLineProfile f).degree k.val) i s j)) := by
  have hc := sumFiberCoordinates_derivative P marking
    (fun k : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
      (PositivePart.freeLineProfile f).degree k.val)
    marking.map i c hchart D s
  have hc' : positiveDerivative f i c hchart D s =
      (positiveFiberCoordinates f i c hchart).symm
        (fun j => D.val (sumCoefficient P marking
          (fun k : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
            (PositivePart.freeLineProfile f).degree k.val) i s j)) := by
    apply (positiveFiberCoordinates f i c hchart).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hc
  change fiberComposition f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)
        (ambientDerivative f i c hchart D
          (onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f) s)) = _
  rw [positiveDerivative_inclusion f i c hchart D s hs, hc']
  rfl

theorem fixedLineVariation_derivative_formula
    {n : ℕ} {X : ContactFanoManifold n}
    (H : HomSpacePresentation P X.variety) (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (v : HomDeformation.FixedLineLift H f x hx) :
    nodeSectionDerivative f x hx i c hchart D
        (HomDeformation.fixedLineVariation H f x hx v) =
      positiveNodeFrameMap f x hx i c hchart
        (fun j => D.val (sumCoefficient P marking
          (fun k : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
            (PositivePart.freeLineProfile f).degree k.val) i
          (HomDeformation.fixedLinePositiveVariation H f x hx v) j)) := by
  rw [← HomDeformation.fixedLinePositiveVariation_inclusion H f x hx v]
  exact nodeSectionDerivative_positive_formula f x hx i c hchart D
    (HomDeformation.fixedLinePositiveVariation H f x hx v)
    (HomDeformation.fixedLinePositiveVariation_node_zero H f x hx v)

/-! ### Scalar normalization on every smaller source neighborhood -/

/-- Function evaluation is the actual appLE of the specified point. The
open need only contain the point; it need not be the full affine chart. -/
def localRingValue {Y : Scheme} (x : ComplexBase ⟶ Y)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) : RingSections Y U →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ hU).hom

theorem localRingValue_restrict {Y : Scheme} (x : ComplexBase ⟶ Y)
    {U V : Y.Opens} (hUV : U ≤ V) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (a : RingSections Y V) :
    localRingValue x U hU (Y.presheaf.map (homOfLE hUV).op a) =
      localRingValue x V hV a := by
  have h := x.map_appLE hU (homOfLE hUV).op
  have hv := congrArg (fun k => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (k a)) h
  exact hv

/-- appLE through an actual open factorization agrees with the canonical
top-section comparison and the actual map from the complex point. -/
theorem pointFactor_appLE {Y : Scheme} (U : Y.Opens)
    (q : ComplexBase ⟶ U.toScheme) (x : ComplexBase ⟶ Y)
    (hq : q ≫ U.ι = x) (hU : ⊤ ≤ x ⁻¹ᵁ U) :
    x.appLE U ⊤ hU = U.topIso.inv ≫ q.appTop := by
  subst x
  have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE] <;> congr 1
  have h := Scheme.Hom.appLE_comp_appLE q U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_rfl
  rw [hι] at h
  exact h.symm.trans (congrArg (fun k => U.topIso.inv ≫ k)
    (Scheme.Hom.appLE_eq_app q (U := ⊤)))

theorem localRingValue_chart (x : ComplexBase ⟶ ProjectiveLine)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (hi : ⊤ ≤ x ⁻¹ᵁ chartOpen i) (a : RingSections ProjectiveLine (chartOpen i)) :
    localRingValue x (chartOpen i) hi a =
      (Polynomial.aeval c) (polynomialChartRingEquiv i a) := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (x.appLE (chartOpen i) ⊤ hi a) = _
  rw [pointFactor_appLE (chartOpen i) (P1TwistEvaluation.pointInOpen i c) x
    ((P1TwistEvaluation.pointInOpen_ι i c).trans hchart) hi]
  exact P1TwistEvaluation.pointInOpen_ring_value i c a

/-- Coefficients in the actual restricted twist frames. These are regular
functions on any smaller source neighborhood, including a preimage of a
chosen target chart intersected with the source chart. -/
def sumLocalCoefficient (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ) (i : Fin 2)
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i)
    (s : CSections P.structureMap (∐ twistFamily Q p a)) (j : I) :
    RingSections ProjectiveLine U :=
  LocalFrames.coordinates
    (LocalFrames.restrict (homOfLE hU) (twistOverFrame Q p (a j) i))
    (TwoChartSections.restrictValue (projectiveTwist Q p (a j)).sheaf le_top
      (onCSections P.structureMap (Sigma.π (twistFamily Q p a) j) s))

theorem sumLocalCoefficient_restrict
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ) (i : Fin 2)
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i)
    (s : CSections P.structureMap (∐ twistFamily Q p a)) (j : I) :
    sumLocalCoefficient Q p a i U hU s j =
      ProjectiveLine.presheaf.map (homOfLE hU).op
        (LocalFrames.coordinates (twistOverFrame Q p (a j) i)
          (TwoChartSections.restrictValue (projectiveTwist Q p (a j)).sheaf le_top
            (onCSections P.structureMap (Sigma.π (twistFamily Q p a) j) s))) := by
  have h := LocalFrames.coordinates_restrict (homOfLE hU)
    (twistOverFrame Q p (a j) i)
    (TwoChartSections.restrictValue (projectiveTwist Q p (a j)).sheaf le_top
      (onCSections P.structureMap (Sigma.π (twistFamily Q p a) j) s))
  change LocalFrames.coordinates
      (LocalFrames.restrict (homOfLE hU) (twistOverFrame Q p (a j) i))
      (TwoChartSections.restrictValue (projectiveTwist Q p (a j)).sheaf hU
        (TwoChartSections.restrictValue (projectiveTwist Q p (a j)).sheaf le_top
          (onCSections P.structureMap (Sigma.π (twistFamily Q p a) j) s))) = _ at h
  rw [TwoChartSections.restrictValue_comp] at h
  exact h

def localFrameVector (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ) (i : Fin 2)
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i) (j : I) :
    SectionsOn (∐ twistFamily Q p a) U :=
  (Sigma.ι (twistFamily Q p a) j).app U
    (LocalFrames.generator
      (LocalFrames.restrict (homOfLE hU) (twistOverFrame Q p (a j) i)))

/-- Actual reconstruction on every smaller open, using the actual sheaf
inclusions. No global-generation assumption enters this local identity. -/
theorem localSection_reconstruct (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint Q) {I : Type} [Fintype I] (a : I → ℤ) (i : Fin 2)
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i)
    (s : CSections P.structureMap (∐ twistFamily Q p a)) :
    (∑ j, sumLocalCoefficient Q p a i U hU s j •
      localFrameVector Q p a i U hU j) =
        TwoChartSections.restrictValue (∐ twistFamily Q p a) le_top s := by
  calc
    _ = ∑ j, (Sigma.ι (twistFamily Q p a) j).app U
        (sumLocalCoefficient Q p a i U hU s j • LocalFrames.generator
          (LocalFrames.restrict (homOfLE hU) (twistOverFrame Q p (a j) i))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (Scheme.Modules.Hom.app_smul (Sigma.ι (twistFamily Q p a) j) _ _).symm
    _ = ∑ j, (Sigma.ι (twistFamily Q p a) j).app U
        (TwoChartSections.restrictValue (projectiveTwist Q p (a j)).sheaf le_top
          (onCSections P.structureMap (Sigma.π (twistFamily Q p a) j) s)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [sumLocalCoefficient, LocalFrames.reconstruct]
    _ = ∑ j, (Sigma.ι (twistFamily Q p a) j).app U
        ((Sigma.π (twistFamily Q p a) j).app U
          (TwoChartSections.restrictValue (∐ twistFamily Q p a) le_top s)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply congrArg ((Sigma.ι (twistFamily Q p a) j).app U)
      exact sheafHom_naturality (Sigma.π (twistFamily Q p a) j) (homOfLE le_top) s
    _ = _ := DirectSumCech.coproduct_section_total (twistFamily Q p a) U _

/-- The coefficient values vanish on every smaller neighborhood of the
same point. This uses actual restriction and point evaluation rather than
assuming equality of values in unrelated coordinate rings. -/
theorem sumLocalCoefficient_value_zero
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i) (hxU : ⊤ ≤ x ⁻¹ᵁ U)
    (s : CSections P.structureMap (∐ twistFamily Q p a))
    (hs : evaluateSection P.structureMap (∐ twistFamily Q p a) x hx s = 0)
    (j : I) : localRingValue x U hxU (sumLocalCoefficient Q p a i U hU s j) = 0 := by
  have hi : ⊤ ≤ x ⁻¹ᵁ chartOpen i := by
    rw [← hchart, pointMap_preimage_chart]
    simp
  rw [sumLocalCoefficient_restrict,
    localRingValue_restrict x hU hxU hi, localRingValue_chart x i c hchart hi]
  exact sumCoefficient_value_zero Q p a x hx i c hchart s hs j

/-- The moving-frame calculation normalized on every smaller source
open. `ell` may be the actual local evaluation against a pulled-back
cotangent section. The point evaluation is the actual scheme map, and
the coefficient zeroes are proved from the actual section's node value.

Only the additive and point-Leibniz laws of the local derivation are
needed; an actual normalized dual-number derivative supplies those laws. -/
theorem localFunctional_derivative_at_zero
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i) (hxU : ⊤ ≤ x ⁻¹ᵁ U)
    (δ : RingSections ProjectiveLine U →+ ℂ)
    (hδ : ∀ r t, δ (r * t) =
      localRingValue x U hxU r * δ t + localRingValue x U hxU t * δ r)
    (ell : SectionsOn (∐ twistFamily Q p a) U →ₗ[RingSections ProjectiveLine U]
      RingSections ProjectiveLine U)
    (s : CSections P.structureMap (∐ twistFamily Q p a))
    (hs : evaluateSection P.structureMap (∐ twistFamily Q p a) x hx s = 0) :
    δ (ell (TwoChartSections.restrictValue (∐ twistFamily Q p a) le_top s)) =
      ∑ j, δ (sumLocalCoefficient Q p a i U hU s j) *
        localRingValue x U hxU (ell (localFrameVector Q p a i U hU j)) := by
  rw [← localSection_reconstruct Q p a i U hU s, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ell.map_smul]
  change δ (sumLocalCoefficient Q p a i U hU s j *
    ell (localFrameVector Q p a i U hU j)) = _
  rw [hδ, sumLocalCoefficient_value_zero Q p a x hx i c hchart U hU hxU s hs j,
    zero_mul, zero_add, mul_comm]

/-- Direct normalization for the actual positive lift of a fixed-node
Hom deformation. No node-zero section or vanishing coefficient is an input. -/
theorem fixedLinePositiveVariation_localFunctional
    {n : ℕ} {X : ContactFanoManifold n}
    (H : HomSpacePresentation P X.variety) (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = marking.map)
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i)
    (hmark : ⊤ ≤ marking.map ⁻¹ᵁ U)
    (δ : RingSections ProjectiveLine U →+ ℂ)
    (hδ : ∀ r t, δ (r * t) =
      localRingValue marking.map U hmark r * δ t +
        localRingValue marking.map U hmark t * δ r)
    (ell : SectionsOn (PositivePart.freeLinePositiveBundle f).sheaf U
      →ₗ[RingSections ProjectiveLine U] RingSections ProjectiveLine U)
    (v : HomDeformation.FixedLineLift H f x hx) :
    δ (ell (TwoChartSections.restrictValue (PositivePart.freeLinePositiveBundle f).sheaf
      le_top (HomDeformation.fixedLinePositiveVariation H f x hx v))) =
      ∑ j : PositivePart.PositiveIndex (PositivePart.freeLineProfile f),
        δ (sumLocalCoefficient P marking
          (fun k : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
            (PositivePart.freeLineProfile f).degree k.val) i U hU
          (HomDeformation.fixedLinePositiveVariation H f x hx v) j) *
        localRingValue marking.map U hmark
          (ell (localFrameVector P marking
            (fun k : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
              (PositivePart.freeLineProfile f).degree k.val) i U hU j)) :=
  localFunctional_derivative_at_zero P marking _ marking.map marking.overC
    i c hchart U hU hmark δ hδ ell
    (HomDeformation.fixedLinePositiveVariation H f x hx v)
    (HomDeformation.fixedLinePositiveVariation_node_zero H f x hx v)

/-! ### Evaluation of the local pairing in the actual fiber -/

/-- Pull a local section along the actual point and restrict to all of
Spec(C). This keeps the genuine pullback sheaf as its codomain. -/
def localFiberValue {Y : Scheme} (x : ComplexBase ⟶ Y) (E : OModule Y)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : SectionsOn E U) : Fiber E x :=
  (pullbackModule x E).presheaf.map (homOfLE hU).op (pullLocalSection x E U s)

theorem localFiberValue_global {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (E : OModule Y) (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (s : CSections sY E) :
    localFiberValue x E U hU (TwoChartSections.restrictValue E le_top s) =
      evaluateSection sY E x hx s := by
  have hn := (sheafHom_naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction x).unit.app E)
    (homOfLE (show U ≤ ⊤ from le_top)) s).symm
  change pullLocalSection x E U (TwoChartSections.restrictValue E le_top s) =
    (pullbackModule x E).presheaf.map (homOfLE (show x ⁻¹ᵁ U ≤ ⊤ from le_top)).op
      (pullLocalSection x E ⊤ s) at hn
  unfold localFiberValue
  rw [hn, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  change (pullbackModule x E).presheaf.map (𝟙 (op ⊤))
      (pullLocalSection x E ⊤ s) = _
  rw [CategoryTheory.Functor.map_id]
  change pullLocalSection x E ⊤ s = sectionValue (pullSection x (sectionFromValue s))
  rw [pullSection_value, sectionFromValue_spec]
  rfl

theorem localFiberValue_map {Y : Scheme} (x : ComplexBase ⟶ Y)
    {E F : OModule Y} (h : E ⟶ F) (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (s : SectionsOn E U) :
    localFiberValue x F U hU (h.app U s) = fiberMap h x (localFiberValue x E U hU s) := by
  unfold localFiberValue
  rw [LeviFiberGeometry.pullLocalSection_map]
  exact sheafHom_naturality ((Scheme.Modules.pullback x).map h)
    (homOfLE hU) (pullLocalSection x E U s)

theorem localFiberValue_pair {Y : Scheme} (x : ComplexBase ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : SectionsOn E U) (t : SectionsOn F U) :
    LeviFiberGeometry.fiberPair b x (localFiberValue x E U hU s)
        (localFiberValue x F U hU t) = localFiberValue x G U hU (b.apply U s t) := by
  change (pullbackPair x b).apply ⊤
      ((pullbackModule x E).presheaf.map (homOfLE hU).op (pullLocalSection x E U s))
      ((pullbackModule x F).presheaf.map (homOfLE hU).op (pullLocalSection x F U t)) = _
  rw [← (pullbackPair x b).naturality]
  rw [pullbackPair_normalized]
  rfl

/-- The scalar fiber is read through the actual unit-pullback isomorphism
and the canonical functions of Spec(C). -/
def scalarFiberValue {Y : Scheme} (x : ComplexBase ⟶ Y) :
    Fiber (structureModule Y) x ≃ₗ[ℂ] ℂ :=
  FrameEvaluation.complexFrameCoordinatesLinearEquiv (unitPullbackIso x).symm

theorem scalarFiberValue_local {Y : Scheme} (x : ComplexBase ⟶ Y)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (r : RingSections Y U) :
    scalarFiberValue x (localFiberValue x (structureModule Y) U hU r) =
      localRingValue x U hU r := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((unitPullbackMap x).app ⊤
      ((pullbackModule x (structureModule Y)).presheaf.map (homOfLE hU).op
        (pullLocalSection x (structureModule Y) U r))) = _
  rw [← sheafHom_naturality]
  have hu : (unitPullbackMap x).app (x ⁻¹ᵁ U)
      (pullLocalSection x (structureModule Y) U r) = x.app U r := by
    exact congrArg (fun k : structureModule Y ⟶
      (Scheme.Modules.pushforward x).obj (structureModule ComplexBase) => k.app U r)
      (unitPullbackMap_adjoint x)
  rw [hu]
  rfl

/-- A local section of the second argument defines a scalar functional
on the actual first fiber using the actual pulled-back pairing. -/
def localScalarPairing {Y : Scheme} (x : ComplexBase ⟶ Y)
    {E F : OModule Y} (b : SheafBilinearMap E F (structureModule Y))
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (t : SectionsOn F U) :
    Fiber E x →ₗ[ℂ] ℂ :=
  (scalarFiberValue x).toLinearMap.comp
    ((LeviFiberGeometry.fiberPair b x).flip (localFiberValue x F U hU t))

theorem localScalarPairing_value {Y : Scheme} (x : ComplexBase ⟶ Y)
    {E F : OModule Y} (b : SheafBilinearMap E F (structureModule Y))
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (t : SectionsOn F U) (s : SectionsOn E U) :
    localScalarPairing x b U hU t (localFiberValue x E U hU s) =
      localRingValue x U hU (b.apply U s t) := by
  change scalarFiberValue x
    (LeviFiberGeometry.fiberPair b x (localFiberValue x E U hU s)
      (localFiberValue x F U hU t)) = _
  rw [localFiberValue_pair, scalarFiberValue_local]

/-- The actual restricted positive-frame vector is the restriction of its
actual normalized global generator, after the actual summand inclusion. -/
theorem localFrameVector_global_generator
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ) (ha : ∀ j, 0 ≤ a j) (i : Fin 2)
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i) (j : I) :
    localFrameVector Q p a i U hU j =
      TwoChartSections.restrictValue (∐ twistFamily Q p a) le_top
        (onCSections P.structureMap (Sigma.ι (twistFamily Q p a) j)
          (chartGenerator Q p (a j) (ha j) i)) := by
  unfold localFrameVector
  rw [← LocalFrames.generator_restrict, ← chartGenerator_restrict Q p (a j) (ha j) i]
  have hr := TwoChartSections.restrictValue_comp
    (projectiveTwist Q p (a j)).sheaf hU (show chartOpen i ≤ ⊤ from le_top)
    (chartGenerator Q p (a j) (ha j) i)
  change (Sigma.ι (twistFamily Q p a) j).app U
      (TwoChartSections.restrictValue (projectiveTwist Q p (a j)).sheaf hU
        (TwoChartSections.restrictValue (projectiveTwist Q p (a j)).sheaf le_top
          (chartGenerator Q p (a j) (ha j) i))) = _
  rw [hr]
  exact (sheafHom_naturality (Sigma.ι (twistFamily Q p a) j) (homOfLE le_top)
    (chartGenerator Q p (a j) (ha j) i)).symm

theorem localFrameVector_fiber
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ) (ha : ∀ j, 0 ≤ a j)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i) (hxU : ⊤ ≤ x ⁻¹ᵁ U) (j : I) :
    localFiberValue x (∐ twistFamily Q p a) U hxU (localFrameVector Q p a i U hU j) =
      fiberMap (Sigma.ι (twistFamily Q p a) j) x
        ((twistFiberCoordinates Q p (a j) x i c hchart).symm 1) := by
  rw [localFrameVector_global_generator Q p a ha i U hU j,
    localFiberValue_global P.structureMap x hx,
    PositiveQuotient.evaluateSection_naturality]
  exact congrArg (fiberMap (Sigma.ι (twistFamily Q p a) j) x)
    (chartGenerator_fiber Q p (a j) (ha j) x hx i c hchart)

theorem sumDerivative_localFrames
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ) (ha : ∀ j, 0 ≤ a j)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i) (hxU : ⊤ ≤ x ⁻¹ᵁ U)
    (s : CSections P.structureMap (∐ twistFamily Q p a)) :
    sumDerivative Q p a x i c hchart D s =
      ∑ j, D.val (sumCoefficient Q p a i s j) •
        localFiberValue x (∐ twistFamily Q p a) U hxU (localFrameVector Q p a i U hU j) := by
  simp only [sumDerivative, LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [localFrameVector_fiber Q p a ha x hx i c hchart U hU hxU j, ← map_smul]
  apply congrArg (fiberMap (Sigma.ι (twistFamily Q p a) j) x)
  apply (twistFiberCoordinates Q p (a j) x i c hchart).injective
  rw [twistDerivative_coordinates, map_smul, LinearEquiv.apply_symm_apply,
    smul_eq_mul, mul_one]
  rfl

/-- Normalization of the source derivative against an actual local
pairing. The only compatibility premise is the explicit restriction law
between the two genuine rings of functions; the actual source dual-number
map supplies that law. In particular no equality with the desired velocity
differential and no arbitrary tangent-space identification is assumed. -/
theorem localPairing_derivative_at_zero
    (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {I : Type} [Fintype I] (a : I → ℤ) (ha : ∀ j, 0 ≤ a j)
    (x : ComplexBase ⟶ ProjectiveLine) (hx : x ≫ P.structureMap = 𝟙 ComplexBase)
    (i : Fin 2) (c : ℂ) (hchart : pointMap i c = x)
    (D : Infinitesimal.Tangent (Polynomial ℂ) (Polynomial.aeval c))
    (U : ProjectiveLine.Opens) (hU : U ≤ chartOpen i) (hxU : ⊤ ≤ x ⁻¹ᵁ U)
    (δ : RingSections ProjectiveLine U →+ ℂ)
    (hδ : ∀ r t, δ (r * t) =
      localRingValue x U hxU r * δ t + localRingValue x U hxU t * δ r)
    (hδchart : ∀ r : RingSections ProjectiveLine (chartOpen i),
      δ (ProjectiveLine.presheaf.map (homOfLE hU).op r) =
        D.val (polynomialChartRingEquiv i r))
    {F : OModule ProjectiveLine}
    (b : SheafBilinearMap (∐ twistFamily Q p a) F (structureModule ProjectiveLine))
    (t : SectionsOn F U)
    (s : CSections P.structureMap (∐ twistFamily Q p a))
    (hs : evaluateSection P.structureMap (∐ twistFamily Q p a) x hx s = 0) :
    δ (b.apply U (TwoChartSections.restrictValue (∐ twistFamily Q p a) le_top s) t) =
      localScalarPairing x b U hxU t (sumDerivative Q p a x i c hchart D s) := by
  have hc : ∀ j, δ (sumLocalCoefficient Q p a i U hU s j) =
      D.val (sumCoefficient Q p a i s j) := by
    intro j
    rw [sumLocalCoefficient_restrict, hδchart]
    rfl
  trans ∑ j, δ (sumLocalCoefficient Q p a i U hU s j) *
    localRingValue x U hxU (b.apply U (localFrameVector Q p a i U hU j) t)
  · exact localFunctional_derivative_at_zero Q p a x hx i c hchart U hU hxU
      δ hδ ((b.apply U).flip t) s hs
  · rw [sumDerivative_localFrames Q p a ha x hx i c hchart D U hU hxU s, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hc, map_smul, localScalarPairing_value]
    rfl

end LeBrunSalamon.Construction.Lines.PositiveFrame

end

/-!
## Actual affine parameter directions feed the fixed-line variation

An affine chart mapping to the fixed-node Hom scheme supplies point
derivations. We realize them as dual-number scheme points and pull back the
actual universal family. This also applies to a reduced or locally closed
parameter subspace: no identification of its tangent space with all sections
of the curve's normal or tangent bundle is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.AffineParameterVariation

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (f : FreeLine X)
variable (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
variable (A : Charts.PointedAffine)
variable (g : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
variable (hat : A.point.val ≫ g.val =
  (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hx).val)

/-- The actual Hom point obtained from a point derivation on the chart. -/
def pointLift (D : A.Tangent) : HomDeformation.FixedLineLift H f x hx :=
  Charts.AffineTangentLift.push g.val g.property hat
    (Charts.AffineTangentLift.lift A D)

theorem pointLift_map (D : A.Tangent) :
    (pointLift H f x hx A g hat D).map =
      (Charts.AffineTangentLift.lift A D).map ≫ g.val := rfl

/-- The curve deformation comes from the original Hom evaluation map. -/
def deformation (D : A.Tangent) :
    FamilyVariation.Deformation P.structureMap X.variety.structureMap f.curve.map :=
  HomDeformation.deformationOfCurve P marking H x f.curve.map f.curve.overC hx
    (pointLift H f x hx A g hat D)

theorem deformation_fixedSource (D : A.Tangent) :
    (deformation H f x hx A g hat D).IsFixedAlong marking.map marking.overC :=
  HomDeformation.deformationOfCurve_fixedSource P marking H x
    f.curve.map f.curve.overC hx (pointLift H f x hx A g hat D)

/-- The normalized infinitesimal section associated with the chart direction. -/
def variation (D : A.Tangent) :
    CSections P.structureMap
      (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap)) :=
  (deformation H f x hx A g hat D).variation X.variety

theorem variation_node_zero (D : A.Tangent) :
    nodeEvaluation f x hx (variation H f x hx A g hat D) = 0 :=
  (deformation H f x hx A g hat D).nodeEvaluation_zero f x hx
    (deformation_fixedSource H f x hx A g hat D)

/-- Every actual chart direction has its unique node-zero positive lift.
The required vanishing is derived from the actual fixed-node equation. -/
theorem positiveLift_existsUnique (D : A.Tangent) :
    ∃! s : CSections P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf,
      onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f) s =
        variation H f x hx A g hat D ∧
      evaluateSection P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf
        marking.map marking.overC s = 0 :=
  (deformation H f x hx A g hat D).positiveLift_existsUnique f x hx
    (deformation_fixedSource H f x hx A g hat D)

/-- Restricting a parameter chart first or lifting its actual differential
first gives exactly the same fixed-node Hom point. -/
theorem pointLift_chartChange (B : Charts.PointedAffine) (h : Charts.Hom B A)
    (D : B.Tangent) :
    (pointLift H f x hx A g hat (h.differential D)).map =
      (Charts.AffineTangentLift.lift B D).map ≫ h.map ≫ g.val := by
  rw [pointLift_map, ← Charts.AffineTangentLift.lift_natural]
  exact Category.assoc _ _ _

/-- Source and parameter restriction commute for precisely the infinitesimal
Hom point constructed from this chart direction. -/
theorem mixed_restrictions_interchange (τ : HomFirstJet.SourceLift P marking)
    (D : A.Tangent) :
    ((HomFirstJet.deformation P marking H x τ).pullback
      (pointLift H f x hx A g hat D).map (pointLift H f x hx A g hat D).overC).map =
      MixedFamily.swap ≫
        ((deformation H f x hx A g hat D).pullback τ.map τ.overC).map := by
  exact MixedFamily.restrictions_interchange P marking H x τ
    (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hx)
    (pointLift H f x hx A g hat D)

end LeBrunSalamon.Construction.Lines.AffineParameterVariation

end

/-!
## Local target functions and the actual mixed derivative

Target functions must be allowed on a neighborhood of the marked image:
global functions on a proper target alone do not detect its tangent vectors.
The support assertions below are derived from the actual nilpotent test
schemes. No rectangular open subset of the source product is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.LocalVelocityComparison

/-- The canonical comparison of the base-change of the identity with Dual. -/
def dualBaseInclusion : Infinitesimal.DualScheme ⟶ DualThickening.space (𝟙 ComplexBase) :=
  pullback.lift Infinitesimal.dualToC (𝟙 Infinitesimal.DualScheme) (by simp)

@[simp] theorem dualBaseInclusion_parameter :
    dualBaseInclusion ≫ DualThickening.parameter (𝟙 ComplexBase) =
      𝟙 Infinitesimal.DualScheme := by
  simp [dualBaseInclusion, DualThickening.parameter]

/-- Point surjectivity of the original dual-number reduction follows from
the reviewed nilpotent-thickening statement by actual pullback projections. -/
theorem origin_surjective : Function.Surjective Infinitesimal.origin := by
  intro z
  obtain ⟨y, hy⟩ :=
    StandardInputs.InfinitesimalGeometry.dualThickening_zeroSection_surjective
      (𝟙 ComplexBase) (dualBaseInclusion z)
  refine ⟨y, ?_⟩
  have h := congrArg (DualThickening.parameter (𝟙 ComplexBase)) hy
  change (DualThickening.zeroSection (𝟙 ComplexBase) ≫
      DualThickening.parameter (𝟙 ComplexBase)) y =
    (dualBaseInclusion ≫ DualThickening.parameter (𝟙 ComplexBase)) z at h
  rw [DualThickening.zeroSection_parameter, Category.id_comp,
    dualBaseInclusion_parameter] at h
  exact h

/-- An infinitesimal point has exactly the support of its reduction. -/
theorem pointLift_range {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (v : Infinitesimal.PointLift Y sY y) : Set.range v.map = Set.range y.val := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨c, rfl⟩ := origin_surjective z
    refine ⟨c, ?_⟩
    exact (congrArg (fun k : ComplexBase ⟶ Y => k c) v.reduces).symm
  · rintro _ ⟨c, rfl⟩
    refine ⟨Infinitesimal.origin c, ?_⟩
    exact congrArg (fun k : ComplexBase ⟶ Y => k c) v.reduces

theorem pointLift_top_le_preimage {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (v : Infinitesimal.PointLift Y sY y) (U : Y.Opens)
    (hU : Set.range y.val ⊆ U) : ⊤ ≤ v.map ⁻¹ᵁ U := by
  intro z _
  apply hU
  rw [← pointLift_range v]
  exact Set.mem_range_self z

/-- A constant-node family is supported in every target open containing
that node, regardless of the size or affineness of the parameter scheme. -/
theorem constant_top_le_preimage {Y Z : Scheme}
    (sY : Y ⟶ ComplexBase) (x : ComplexBase ⟶ Z)
    (U : Z.Opens) (hU : Set.range x ⊆ U) : ⊤ ≤ (sY ≫ x) ⁻¹ᵁ U := by
  intro y _
  exact hU ⟨sY y, rfl⟩

/-- Local target functions pull back along the full source first jet, even
when the original curve is not contained in the target open. -/
theorem sourceLift_top_le_preimage (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (τ : HomFirstJet.SourceLift P p)
    {Z : Scheme} (f : ProjectiveLine ⟶ Z) (x : ComplexBase ⟶ Z)
    (hx : p.map ≫ f = x) (U : Z.Opens) (hU : Set.range x ⊆ U) :
    ⊤ ≤ τ.map ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  apply pointLift_top_le_preimage τ (f ⁻¹ᵁ U)
  rintro _ ⟨c, rfl⟩
  have he := congrArg (fun k : ComplexBase ⟶ Z => k c) hx
  change f (p.map c) ∈ U
  rw [show f (p.map c) = x c from he]
  exact hU ⟨c, rfl⟩

/-- The actual parameter lift stays inside the domain of every velocity
coefficient obtained from a local target function at x. -/
theorem parameterLift_top_le_preimage {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (v : Infinitesimal.PointLift Y sY y) (x : ComplexBase ⟶ Z)
    (U : Z.Opens) (hU : Set.range x ⊆ U) :
    ⊤ ≤ v.map ⁻¹ᵁ ((sY ≫ x) ⁻¹ᵁ U) := by
  intro z _
  exact hU ⟨sY (v.map z), rfl⟩

/-- Differentiation of a local function along the specified actual dual
point. Both its scalar structure and its infinitesimal normalization are
the canonical ones on the original scheme. -/
def derivativeAlong {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (g : Infinitesimal.DualScheme ⟶ Y)
    (hg : g ≫ sY = Infinitesimal.dualToC)
    (U : Y.Opens) (hU : ⊤ ≤ g ⁻¹ᵁ U) :
    SectionAlgebra.Functions sY U →ₗ[ℂ] ℂ :=
  MixedJet.dualCoefficient.comp
    (DualMixedBridge.dualGlobalEquiv.toLinearMap.comp
      (SectionAlgebra.onFunctionsLE g hg U ⊤ hU).toLinearMap)

theorem derivativeAlong_apply {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (g : Infinitesimal.DualScheme ⟶ Y)
    (hg : g ≫ sY = Infinitesimal.dualToC)
    (U : Y.Opens) (hU : ⊤ ≤ g ⁻¹ᵁ U) (a : RingSections Y U) :
    derivativeAlong g hg U hU a =
      MixedJet.dualCoefficient
        (DualMixedBridge.dualGlobalEquiv (g.appLE U ⊤ hU a)) := rfl

/-- On an actual affine chart, the constructed lift differentiates its
original function by precisely the original point derivation. -/
theorem derivativeAlong_affineLift (A : Charts.PointedAffine)
    (D : A.Tangent) (a : A.Ring) :
    derivativeAlong (Charts.AffineTangentLift.lift A D).map
      (Charts.AffineTangentLift.lift A D).overC ⊤ (by simp) a = D.val a := by
  exact Charts.AffineTangentLift.lift_linearCoefficient A D a

/-- The actual value of a local function at a complex point, using its
scheme pullback rather than a separately chosen evaluation functional. -/
def valueAt {Y : Scheme} (y : ComplexBase ⟶ Y) (U : Y.Opens)
    (hU : ⊤ ≤ y ⁻¹ᵁ U) : RingSections Y U →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (y.appLE U ⊤ hU).hom

/-- Reduction of a pulled-back local function is its original value at
the center. This is derived from the lift's scheme reduction equation. -/
theorem residue_pullback {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (v : Infinitesimal.PointLift Y sY y) (U : Y.Opens)
    (hy : ⊤ ≤ y.val ⁻¹ᵁ U) (hv : ⊤ ≤ v.map ⁻¹ᵁ U) (a : RingSections Y U) :
    Infinitesimal.residue
        (DualMixedBridge.dualGlobalEquiv (v.map.appLE U ⊤ hv a)) = valueAt y.val U hy a := by
  have hc : v.map.appLE U ⊤ hv ≫ Infinitesimal.origin.appTop =
      y.val.appLE U ⊤ hy := by
    have ht : Infinitesimal.origin.appTop = Infinitesimal.origin.appLE ⊤ ⊤ le_rfl :=
      Infinitesimal.origin.app_eq_appLE
    rw [ht, Scheme.Hom.appLE_comp_appLE]
    exact DualThickening.appLE_of_map_eq v.reduces U ⊤ _ _
  have hn := congrArg (fun k :
      (Spec (CommRingCat.of Infinitesimal.Dual)).presheaf.obj (op ⊤) ⟶
        CommRingCat.of ℂ => k (v.map.appLE U ⊤ hv a))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom Infinitesimal.residue.toRingHom))
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (Infinitesimal.origin.appTop (v.map.appLE U ⊤ hv a)) =
    Infinitesimal.residue (DualMixedBridge.dualGlobalEquiv
      (v.map.appLE U ⊤ hv a)) at hn
  rw [← hn]
  exact congrArg (fun k => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (k a)) hc

/-- The local derivative from an actual point lift obeys Leibniz with
the actual value at its center. This supplies the scalar moving-frame
argument with its required derivation, rather than assuming one. -/
theorem derivativeAlong_leibniz {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (v : Infinitesimal.PointLift Y sY y) (U : Y.Opens)
    (hy : ⊤ ≤ y.val ⁻¹ᵁ U) (hv : ⊤ ≤ v.map ⁻¹ᵁ U)
    (a b : RingSections Y U) :
    derivativeAlong v.map v.overC U hv (a*b) =
      valueAt y.val U hy a * derivativeAlong v.map v.overC U hv b +
        valueAt y.val U hy b * derivativeAlong v.map v.overC U hv a := by
  simp only [derivativeAlong_apply, map_mul]
  rw [MixedJet.dualCoefficient_mul, residue_pullback v U hy hv,
    residue_pullback v U hy hv]

/-- The first-order expansion is normalized by both the actual center
value and the actual derivative on the original open. -/
theorem pullback_local_normalForm {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (v : Infinitesimal.PointLift Y sY y) (U : Y.Opens)
    (hy : ⊤ ≤ y.val ⁻¹ᵁ U) (hv : ⊤ ≤ v.map ⁻¹ᵁ U)
    (a : RingSections Y U) :
    DualMixedBridge.dualGlobalEquiv (v.map.appLE U ⊤ hv a) =
      algebraMap ℂ Infinitesimal.Dual (valueAt y.val U hy a) +
        Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
          (derivativeAlong v.map v.overC U hv a) := by
  have hr := Infinitesimal.dual_normalForm_reconstruct
    (DualMixedBridge.dualGlobalEquiv (v.map.appLE U ⊤ hv a))
  refine hr.trans ?_
  exact congrArg (fun c : ℂ => algebraMap ℂ Infinitesimal.Dual c +
    Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
      (derivativeAlong v.map v.overC U hv a)) (residue_pullback v U hy hv a)

/-- Equality of two actual restrictions on the full double thickening
implies equality of their successive derivatives on each local target
function. The hypotheses concern only maps and function domains. -/
theorem mixed_derivative_of_restrictions_eq {Y Z X : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} {h : Z ⟶ X}
    (F : FamilyVariation.Deformation sY sX f)
    (G : FamilyVariation.Deformation sZ sX h)
    (v : Infinitesimal.DualScheme ⟶ Y) (hv : v ≫ sY = Infinitesimal.dualToC)
    (τ : Infinitesimal.DualScheme ⟶ Z) (hτ : τ ≫ sZ = Infinitesimal.dualToC)
    (heq : (F.pullback v hv).map = MixedFamily.swap ≫ (G.pullback τ hτ).map)
    (U : X.Opens)
    (hF : ⊤ ≤ v ⁻¹ᵁ (f ⁻¹ᵁ U)) (hG : ⊤ ≤ τ ⁻¹ᵁ (h ⁻¹ᵁ U))
    (a : RingSections X U) :
    derivativeAlong v hv (f ⁻¹ᵁ U) hF (F.onFunction U a) =
      derivativeAlong τ hτ (h ⁻¹ᵁ U) hG (G.onFunction U a) := by
  have hm := DualMixedBridge.mixedCoefficient_restrictions
    (F.pullback v hv).map (G.pullback τ hτ).map heq U
    (DualMixedBridge.actualPullback_support G τ hτ U hG)
    (DualMixedBridge.actualPullback_support F v hv U hF) a
  rw [DualMixedBridge.mixedCoefficient_actualPullback,
    DualMixedBridge.mixedCoefficient_actualPullback] at hm
  exact hm

/-- The key mixed derivative identity for the original fixed free line.
The left side differentiates the actual regular velocity coefficient in
the actual Hom direction. The right side differentiates the normalized
deformation section on the source. Every local target function at x is
allowed; no equality of these derivatives has been assumed. -/
theorem fixedLine_mixed_derivative {n : ℕ} {X : ContactFanoManifold n}
    (H : HomSpacePresentation P X.variety) (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (τ : HomFirstJet.SourceLift P marking)
    (v : HomDeformation.FixedLineLift H f x hx)
    (U : X.variety.scheme.Opens) (hU : Set.range x.map ⊆ U)
    (a : RingSections X.variety.scheme U) :
    derivativeAlong v.map v.overC
        ((FixedNodeHom.toC P marking H x ≫ x.map) ⁻¹ᵁ U)
        (parameterLift_top_le_preimage v x.map U hU)
        ((HomFirstJet.deformation P marking H x τ).onFunction U a) =
      derivativeAlong τ.map τ.overC (f.curve.map ⁻¹ᵁ U)
        (sourceLift_top_le_preimage P marking τ f.curve.map x.map hx U hU)
        ((HomDeformation.deformationOfCurve P marking H x
          f.curve.map f.curve.overC hx v).onFunction U a) := by
  apply mixed_derivative_of_restrictions_eq
    (HomFirstJet.deformation P marking H x τ)
    (HomDeformation.deformationOfCurve P marking H x f.curve.map f.curve.overC hx v)
    v.map v.overC τ.map τ.overC
  exact MixedFamily.restrictions_interchange P marking H x τ
    (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hx) v

/-- The same identity written entirely in terms of the actual positive
lift's normalized cotangent pairing. Its positive lift was constructed
from v and its zero value was proved in the previous checkpoint. -/
theorem fixedLine_positive_mixed_derivative {n : ℕ} {X : ContactFanoManifold n}
    (H : HomSpacePresentation P X.variety) (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (τ : HomFirstJet.SourceLift P marking)
    (v : HomDeformation.FixedLineLift H f x hx)
    (U : X.variety.scheme.Opens) (hU : Set.range x.map ⊆ U)
    (a : RingSections X.variety.scheme U) :
    derivativeAlong v.map v.overC
        ((FixedNodeHom.toC P marking H x ≫ x.map) ⁻¹ᵁ U)
        (parameterLift_top_le_preimage v x.map U hU)
        ((HomFirstJet.deformation P marking H x τ).onFunction U a) =
      derivativeAlong τ.map τ.overC (f.curve.map ⁻¹ᵁ U)
        (sourceLift_top_le_preimage P marking τ f.curve.map x.map hx U hU)
        ((TwoChartSections.internalHomSectionAddEquiv _ _
          (sectionFromValue (onCSections P.structureMap
            (PositivePart.freeLinePositiveInclusion f)
            (HomDeformation.fixedLinePositiveVariation H f x hx v)) ≫
              dualBaseChange f.curve.map (cotangentSheaf X.variety.structureMap))).app
          (f.curve.map ⁻¹ᵁ U)
          (pullLocalSection f.curve.map (cotangentSheaf X.variety.structureMap) U
            ((cotangentPresentation X.variety.structureMap).differential.apply U a))) := by
  rw [HomDeformation.fixedLinePositiveVariation_on_differential]
  exact fixedLine_mixed_derivative H f x hx τ v U hU a

end LeBrunSalamon.Construction.Lines.LocalVelocityComparison

end

/-!
## The actual source derivative in the positive-bundle polynomial chart

The source lift at the marking is a genuine map into one standard
polynomial chart. Its pullback of each actual source function is normalized
by the established chart ring equivalence and Gamma--Spec comparison.
Thus the epsilon coefficient is the ordinary polynomial derivative at the
actual coordinate of the marking. Restricting a function to any smaller
open containing the infinitesimal support preserves that derivative.

Unchecked continuation. No additional admission is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames

namespace LeBrunSalamon.Construction.Lines.LocalVelocityComparison

/-- The derivative of a local function is unchanged after restricting
its domain to any smaller open containing the actual infinitesimal support. -/
theorem derivativeAlong_restrict {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (g : Infinitesimal.DualScheme ⟶ Y)
    (hg : g ≫ sY = Infinitesimal.dualToC)
    {U V : Y.Opens} (i : U ⟶ V)
    (hU : ⊤ ≤ g ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ V)
    (a : RingSections Y V) :
    derivativeAlong g hg U hU (Y.presheaf.map i.op a) =
      derivativeAlong g hg V hV a := by
  have hm : Y.presheaf.map i.op ≫ g.appLE U ⊤ hU = g.appLE V ⊤ hV := by
    rw [Scheme.Hom.map_appLE]
  exact congrArg (fun k => MixedJet.dualCoefficient
    (DualMixedBridge.dualGlobalEquiv (k a))) hm

/-- The value of the same function at its actual point is also
independent of such an open restriction. -/
theorem valueAt_restrict {Y : Scheme} (y : ComplexBase ⟶ Y)
    {U V : Y.Opens} (i : U ⟶ V)
    (hU : ⊤ ≤ y ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V)
    (a : RingSections Y V) :
    valueAt y U hU (Y.presheaf.map i.op a) = valueAt y V hV a := by
  have hm : Y.presheaf.map i.op ≫ y.appLE U ⊤ hU = y.appLE V ⊤ hV := by
    rw [Scheme.Hom.map_appLE]
  exact congrArg (fun k => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (k a)) hm

end LeBrunSalamon.Construction.Lines.LocalVelocityComparison

namespace LeBrunSalamon.Construction.Lines.PolynomialSourceLift

open LocalVelocityComparison

theorem point_top_le_chart (i : Fin 2) (c : ℂ) :
    ⊤ ≤ pointMap i c ⁻¹ᵁ chartOpen i := by
  rw [pointMap_preimage_chart]
  simp

theorem mapAt_top_le_chart (i : Fin 2) (c : ℂ) :
    ⊤ ≤ mapAt i c ⁻¹ᵁ chartOpen i := by
  rw [mapAt, Scheme.Hom.comp_preimage, ← polynomialChartInclusion_range i,
    Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]

/-- Full first-order normalization of an actual chart function. The
polynomial is obtained from the pre-existing original Proj chart map. -/
theorem mapAt_function (i : Fin 2) (c : ℂ)
    (h : ⊤ ≤ mapAt i c ⁻¹ᵁ chartOpen i)
    (a : RingSections ProjectiveLine (chartOpen i)) :
    DualMixedBridge.dualGlobalEquiv ((mapAt i c).appLE (chartOpen i) ⊤ h a) =
      Infinitesimal.tangentToDual (Polynomial.aeval c) (derivation c)
        (polynomialChartRingEquiv i a) := by
  let φ := Infinitesimal.tangentToDual (Polynomial.aeval c) (derivation c)
  have hi : ⊤ ≤ (polynomialChartInclusion i) ⁻¹ᵁ chartOpen i := by
    rw [← polynomialChartInclusion_range i, Scheme.Hom.preimage_opensRange]
  have hc : (mapAt i c).appLE (chartOpen i) ⊤ h =
      (polynomialChartInclusion i).appLE (chartOpen i) ⊤ hi ≫
        (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop := by
    have ht : (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop =
        (Spec.map (CommRingCat.ofHom φ.toRingHom)).appLE ⊤ ⊤ le_rfl :=
      (Spec.map (CommRingCat.ofHom φ.toRingHom)).app_eq_appLE
    rw [ht, Scheme.Hom.appLE_comp_appLE]
    rfl
  have hn : (mapAt i c).appLE (chartOpen i) ⊤ h ≫
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom =
      CommRingCat.ofHom (polynomialChartRingEquiv i).toRingHom ≫
        CommRingCat.ofHom φ.toRingHom := by
    rw [hc, Category.assoc, Scheme.ΓSpecIso_naturality,
      ← Category.assoc, ← polynomialChartRingEquiv_eq_appLE]
  exact congrArg (fun k => k a) hn

/-- The actual source lift differentiates precisely by evaluation of the
polynomial derivative at the actual marked coordinate. -/
theorem derivativeAlong_mapAt (i : Fin 2) (c : ℂ)
    (h : ⊤ ≤ mapAt i c ⁻¹ᵁ chartOpen i)
    (a : RingSections ProjectiveLine (chartOpen i)) :
    derivativeAlong (mapAt i c) (mapAt_overC i c) (chartOpen i) h a =
      (derivation c).val (polynomialChartRingEquiv i a) := by
  rw [derivativeAlong_apply, mapAt_function]
  exact Infinitesimal.linearCoefficient_normalForm _ _

/-- At the same actual center, the zero-order coefficient is ordinary
polynomial evaluation. This uses the point lift's actual reduction. -/
theorem valueAt_pointMap (i : Fin 2) (c : ℂ)
    (h : ⊤ ≤ pointMap i c ⁻¹ᵁ chartOpen i)
    (a : RingSections ProjectiveLine (chartOpen i)) :
    valueAt (pointMap i c) (chartOpen i) h a =
      Polynomial.aeval c (polynomialChartRingEquiv i a) := by
  have hr := residue_pullback (liftAt i c) (chartOpen i) h (mapAt_top_le_chart i c) a
  change Infinitesimal.residue
      (DualMixedBridge.dualGlobalEquiv
        ((mapAt i c).appLE (chartOpen i) ⊤ (mapAt_top_le_chart i c) a)) =
    valueAt (pointMap i c) (chartOpen i) h a at hr
  rw [mapAt_function] at hr
  have hp := congrArg (fun q : Polynomial ℂ →ₐ[ℂ] ℂ =>
    q (polynomialChartRingEquiv i a))
      (Infinitesimal.tangentToDual_residue (Polynomial.aeval c) (derivation c))
  exact hr.symm.trans hp

/-- This statement applies when the positive frame and the original
target-function pullback are used only on their common smaller open. -/
theorem derivativeAlong_mapAt_restrict (i : Fin 2) (c : ℂ)
    {U : ProjectiveLine.Opens} (hU : U ≤ chartOpen i)
    (hτ : ⊤ ≤ mapAt i c ⁻¹ᵁ U)
    (a : RingSections ProjectiveLine (chartOpen i)) :
    derivativeAlong (mapAt i c) (mapAt_overC i c) U hτ
        (ProjectiveLine.presheaf.map (homOfLE hU).op a) =
      (derivation c).val (polynomialChartRingEquiv i a) := by
  rw [derivativeAlong_restrict (mapAt i c) (mapAt_overC i c) (homOfLE hU)
    hτ (mapAt_top_le_chart i c)]
  exact derivativeAlong_mapAt i c (mapAt_top_le_chart i c) a

theorem valueAt_pointMap_restrict (i : Fin 2) (c : ℂ)
    {U : ProjectiveLine.Opens} (hU : U ≤ chartOpen i)
    (hp : ⊤ ≤ pointMap i c ⁻¹ᵁ U)
    (a : RingSections ProjectiveLine (chartOpen i)) :
    valueAt (pointMap i c) U hp
        (ProjectiveLine.presheaf.map (homOfLE hU).op a) =
      Polynomial.aeval c (polynomialChartRingEquiv i a) := by
  rw [valueAt_restrict (pointMap i c) (homOfLE hU) hp (point_top_le_chart i c)]
  exact valueAt_pointMap i c (point_top_le_chart i c) a

/-- The chosen source lift at the original marking is normalized in
the same genuine polynomial chart used to select it. -/
theorem derivativeAlong_atMarking (p : ProjectiveLinePoint canonicalProjectiveLine)
    (h : ⊤ ≤ (atMarking p).map ⁻¹ᵁ chartOpen (markingChart p).index)
    (a : RingSections ProjectiveLine (chartOpen (markingChart p).index)) :
    derivativeAlong (atMarking p).map (atMarking p).overC
        (chartOpen (markingChart p).index) h a =
      (derivation (markingChart p).coordinate).val
        (polynomialChartRingEquiv (markingChart p).index a) :=
  derivativeAlong_mapAt (markingChart p).index (markingChart p).coordinate h a

end LeBrunSalamon.Construction.Lines.PolynomialSourceLift

end

/-!
## The actual mixed derivative factors through the positive fiber pairing

The source direction is the normalized nonconstant polynomial lift at the
actual marking. The moving-frame argument is applied to the actual positive
lift and to the actual pulled-back tangent-cotangent evaluation. All local
function domains are retained. The resulting scalar identity is the remaining
normalization needed when identifying the affine velocity target with the
original tangent-sheaf fiber.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.P1Charts

namespace LeBrunSalamon.Construction.Lines.PositiveVelocityPairing

open FamilyVariation LocalVelocityComparison

/-- The actual pulled-back evaluation of tangent vectors on cotangent
vectors, normalized by the original unit-pullback morphism. -/
def pulledEvaluation {Y X : Scheme} (f : Y ⟶ X) (sX : X ⟶ ComplexBase) :
    SheafBilinearMap (pullbackModule f (tangentSheaf sX))
      (pullbackModule f (cotangentSheaf sX)) (structureModule Y) :=
  (pullbackPair f (dualEvaluation (cotangentSheaf sX))).postcompose (unitPullbackMap f)

/-- Pairing the actual variation with any local pulled-back cotangent
section recovers its actual cotangent functional. -/
theorem variation_pairing {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) {sY : Y ⟶ ComplexBase}
    {f : Y ⟶ X.scheme} (D : Deformation sY X.structureMap f)
    (U : Y.Opens) (e : SectionsOn (pullbackModule f (cotangentSheaf X.structureMap)) U) :
    (pulledEvaluation f X.structureMap).apply U
        (TwoChartSections.restrictValue (pullbackModule f (tangentSheaf X.structureMap))
          le_top (D.variation X)) e = D.cotangentHom.app U e := by
  change (unitPullbackMap f).app U
    ((pullbackPair f (dualEvaluation (cotangentSheaf X.structureMap))).apply U
      (TwoChartSections.restrictValue (pullbackModule f (tangentSheaf X.structureMap))
        le_top (D.variation X)) e) = _
  rw [← dualBaseChange_evaluate]
  have hs : TwoChartSections.restrictValue
      (pullbackModule f (tangentSheaf X.structureMap)) le_top (D.variation X) =
        Scheme.Modules.Hom.app (D.section X) U (1 : RingSections Y U) :=
    (ScalarSections.section_app_one (D.section X) U).symm
  rw [hs]
  change (dualEvaluation (pullbackModule f (cotangentSheaf X.structureMap))).apply U
    (Scheme.Modules.Hom.app
      (D.section X ≫ dualBaseChange f (cotangentSheaf X.structureMap)) U
        (1 : RingSections Y U)) e = _
  rw [D.section_normalized]
  exact homSection_evaluate_one D.cotangentHom U e

variable {n : ℕ} {X : ContactFanoManifold n}

/-- Restrict the actual pulled-back evaluation to the actual positive bundle. -/
def positiveEvaluation (f : FreeLine X) :
    SheafBilinearMap (PositivePart.freeLinePositiveBundle f).sheaf
      (pullbackModule f.curve.map (cotangentSheaf X.variety.structureMap))
      (structureModule ProjectiveLine) :=
  (pulledEvaluation f.curve.map X.variety.structureMap).precompose
    (PositivePart.freeLinePositiveInclusion f) (𝟙 _)

theorem positiveVariation_pairing (H : HomSpacePresentation P X.variety)
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (v : HomDeformation.FixedLineLift H f x hx)
    (V : X.variety.scheme.Opens) (a : RingSections X.variety.scheme V) :
    (positiveEvaluation f).apply (f.curve.map ⁻¹ᵁ V)
        (TwoChartSections.restrictValue (PositivePart.freeLinePositiveBundle f).sheaf
          le_top (HomDeformation.fixedLinePositiveVariation H f x hx v))
        (pullLocalSection f.curve.map (cotangentSheaf X.variety.structureMap) V
          ((cotangentPresentation X.variety.structureMap).differential.apply V a)) =
      (HomDeformation.deformationOfCurve P marking H x
        f.curve.map f.curve.overC hx v).onFunction V a := by
  change (pulledEvaluation f.curve.map X.variety.structureMap).apply (f.curve.map ⁻¹ᵁ V)
    ((PositivePart.freeLinePositiveInclusion f).app (f.curve.map ⁻¹ᵁ V)
      (TwoChartSections.restrictValue (PositivePart.freeLinePositiveBundle f).sheaf
        le_top (HomDeformation.fixedLinePositiveVariation H f x hx v))) _ = _
  have hnat := (TwoChartSections.restrictValue_map
    (PositivePart.freeLinePositiveInclusion f)
    (show f.curve.map ⁻¹ᵁ V ≤ ⊤ from le_top)
    (HomDeformation.fixedLinePositiveVariation H f x hx v)).symm
  have hi := congrArg (fun s : CSections P.structureMap
      (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap)) =>
    TwoChartSections.restrictValue
      (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap))
      (show f.curve.map ⁻¹ᵁ V ≤ ⊤ from le_top) s)
    (HomDeformation.fixedLinePositiveVariation_inclusion H f x hx v)
  have hpair := congrArg (fun t : SectionsOn
      (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap)) (f.curve.map ⁻¹ᵁ V) =>
    (pulledEvaluation f.curve.map X.variety.structureMap).apply (f.curve.map ⁻¹ᵁ V) t
      (pullLocalSection f.curve.map (cotangentSheaf X.variety.structureMap) V
        ((cotangentPresentation X.variety.structureMap).differential.apply V a)))
    (hnat.trans hi)
  exact hpair.trans ((variation_pairing X.variety
    (HomDeformation.deformationOfCurve P marking H x f.curve.map f.curve.overC hx v)
    (f.curve.map ⁻¹ᵁ V)
    (pullLocalSection f.curve.map (cotangentSheaf X.variety.structureMap) V
      ((cotangentPresentation X.variety.structureMap).differential.apply V a))).trans
    ((HomDeformation.deformationOfCurve P marking H x
      f.curve.map f.curve.overC hx v).cotangentHom_differential V a))

/-- The genuine local target differential restricted to a common source
neighborhood. This definition does not extend it outside its domain. -/
def localDifferential (f : FreeLine X) (V : X.variety.scheme.Opens)
    (a : RingSections X.variety.scheme V)
    (U : ProjectiveLine.Opens) (hUV : U ≤ f.curve.map ⁻¹ᵁ V) :
    SectionsOn (pullbackModule f.curve.map (cotangentSheaf X.variety.structureMap)) U :=
  TwoChartSections.restrictValue _ hUV
    (pullLocalSection f.curve.map (cotangentSheaf X.variety.structureMap) V
      ((cotangentPresentation X.variety.structureMap).differential.apply V a))

theorem positiveVariation_pairing_restrict (H : HomSpacePresentation P X.variety)
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (v : HomDeformation.FixedLineLift H f x hx)
    (V : X.variety.scheme.Opens) (a : RingSections X.variety.scheme V)
    (U : ProjectiveLine.Opens) (hUV : U ≤ f.curve.map ⁻¹ᵁ V) :
    (positiveEvaluation f).apply U
        (TwoChartSections.restrictValue (PositivePart.freeLinePositiveBundle f).sheaf
          le_top (HomDeformation.fixedLinePositiveVariation H f x hx v))
        (localDifferential f V a U hUV) =
      ProjectiveLine.presheaf.map (homOfLE hUV).op
        ((HomDeformation.deformationOfCurve P marking H x
          f.curve.map f.curve.overC hx v).onFunction V a) := by
  have hn := (positiveEvaluation f).naturality (homOfLE hUV)
    (TwoChartSections.restrictValue (PositivePart.freeLinePositiveBundle f).sheaf
      le_top (HomDeformation.fixedLinePositiveVariation H f x hx v))
    (pullLocalSection f.curve.map (cotangentSheaf X.variety.structureMap) V
      ((cotangentPresentation X.variety.structureMap).differential.apply V a))
  rw [positiveVariation_pairing] at hn
  change ProjectiveLine.presheaf.map (homOfLE hUV).op _ =
    (positiveEvaluation f).apply U
      (TwoChartSections.restrictValue (PositivePart.freeLinePositiveBundle f).sheaf hUV
        (TwoChartSections.restrictValue (PositivePart.freeLinePositiveBundle f).sheaf
          le_top (HomDeformation.fixedLinePositiveVariation H f x hx v)))
      (localDifferential f V a U hUV) at hn
  rw [TwoChartSections.restrictValue_comp] at hn
  exact hn.symm

/-- The actual source lift has support in every source neighborhood of
the original marking. -/
theorem source_support (U : ProjectiveLine.Opens)
    (hmark : ⊤ ≤ marking.map ⁻¹ᵁ U) :
    ⊤ ≤ (PolynomialSourceLift.atMarking marking).map ⁻¹ᵁ U := by
  apply pointLift_top_le_preimage (PolynomialSourceLift.atMarking marking) U
  rintro _ ⟨c, rfl⟩
  exact hmark (show c ∈ (⊤ : ComplexBase.Opens) by trivial)

/-- The local moving-frame derivative uses the actual source lift and
the actual positive section. The center value, its Leibniz law and its
polynomial-coordinate normalization have all been proved. -/
theorem positiveVariation_source_pairing
    (H : HomSpacePresentation P X.variety) (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (v : HomDeformation.FixedLineLift H f x hx)
    (U : ProjectiveLine.Opens)
    (hchart : U ≤ chartOpen (PolynomialSourceLift.markingChart marking).index)
    (hmark : ⊤ ≤ marking.map ⁻¹ᵁ U)
    (t : SectionsOn (pullbackModule f.curve.map (cotangentSheaf X.variety.structureMap)) U) :
    derivativeAlong (PolynomialSourceLift.atMarking marking).map
        (PolynomialSourceLift.atMarking marking).overC U (source_support U hmark)
        ((positiveEvaluation f).apply U
          (TwoChartSections.restrictValue (PositivePart.freeLinePositiveBundle f).sheaf
            le_top (HomDeformation.fixedLinePositiveVariation H f x hx v)) t) =
      PositiveFrame.localScalarPairing marking.map (positiveEvaluation f) U hmark t
        (PositiveFrame.positiveDerivative f
          (PolynomialSourceLift.markingChart marking).index
          (PolynomialSourceLift.markingChart marking).coordinate
          (PolynomialSourceLift.markingChart marking).identifies
          (PolynomialSourceLift.derivation (PolynomialSourceLift.markingChart marking).coordinate)
          (HomDeformation.fixedLinePositiveVariation H f x hx v)) := by
  apply PositiveFrame.localPairing_derivative_at_zero P marking
    (fun j : PositivePart.PositiveIndex (PositivePart.freeLineProfile f) =>
      (PositivePart.freeLineProfile f).degree j.val)
    (fun j => le_of_lt j.property) marking.map marking.overC
    (PolynomialSourceLift.markingChart marking).index
    (PolynomialSourceLift.markingChart marking).coordinate
    (PolynomialSourceLift.markingChart marking).identifies
    (PolynomialSourceLift.derivation (PolynomialSourceLift.markingChart marking).coordinate)
    U hchart hmark
    (derivativeAlong (PolynomialSourceLift.atMarking marking).map
      (PolynomialSourceLift.atMarking marking).overC U (source_support U hmark)).toAddMonoidHom
  · intro r t
    exact derivativeAlong_leibniz (PolynomialSourceLift.atMarking marking)
      U hmark (source_support U hmark) r t
  · intro r
    exact PolynomialSourceLift.derivativeAlong_mapAt_restrict
      (PolynomialSourceLift.markingChart marking).index
      (PolynomialSourceLift.markingChart marking).coordinate hchart
      (source_support U hmark) r
  · exact HomDeformation.fixedLinePositiveVariation_node_zero H f x hx v

/-- On every genuine common source neighborhood, the parameter derivative
of an actual velocity coordinate is evaluation of the actual positive fiber
derivative against the original target differential. No tangent identification
or desired range containment is assumed in this scalar factorization. -/
theorem mixedDerivative_positive_fiber_pairing
    (H : HomSpacePresentation P X.variety) (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (v : HomDeformation.FixedLineLift H f x hx)
    (V : X.variety.scheme.Opens) (hV : Set.range x.map ⊆ V)
    (a : RingSections X.variety.scheme V)
    (U : ProjectiveLine.Opens)
    (hchart : U ≤ chartOpen (PolynomialSourceLift.markingChart marking).index)
    (hUV : U ≤ f.curve.map ⁻¹ᵁ V) (hmark : ⊤ ≤ marking.map ⁻¹ᵁ U) :
    derivativeAlong v.map v.overC
        ((FixedNodeHom.toC P marking H x ≫ x.map) ⁻¹ᵁ V)
        (parameterLift_top_le_preimage v x.map V hV)
        ((HomFirstJet.deformation P marking H x
          (PolynomialSourceLift.atMarking marking)).onFunction V a) =
      PositiveFrame.localScalarPairing marking.map (positiveEvaluation f) U hmark
        (localDifferential f V a U hUV)
        (PositiveFrame.positiveDerivative f
          (PolynomialSourceLift.markingChart marking).index
          (PolynomialSourceLift.markingChart marking).coordinate
          (PolynomialSourceLift.markingChart marking).identifies
          (PolynomialSourceLift.derivation (PolynomialSourceLift.markingChart marking).coordinate)
          (HomDeformation.fixedLinePositiveVariation H f x hx v)) := by
  rw [fixedLine_mixed_derivative H f x hx (PolynomialSourceLift.atMarking marking) v V hV a]
  rw [← derivativeAlong_restrict (PolynomialSourceLift.atMarking marking).map
    (PolynomialSourceLift.atMarking marking).overC (homOfLE hUV) (source_support U hmark)]
  rw [← positiveVariation_pairing_restrict H f x hx v V a U hUV]
  exact positiveVariation_source_pairing H f x hx v U hchart hmark
    (localDifferential f V a U hUV)

end LeBrunSalamon.Construction.Lines.PositiveVelocityPairing

end

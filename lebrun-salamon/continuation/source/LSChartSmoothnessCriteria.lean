import Mathlib

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

/-!
Two standalone published criteria for smooth morphisms.  No project chart,
contact, integrality, or separatedness hypothesis occurs in either input.
The explicit dual-number presentation below supplies only the conventional
test scheme in the tangent-space criterion.
-/

namespace LeBrunSalamon.DualNumberGeometry

/-- The ordinary dual-number algebra over an arbitrary field. -/
def dualIdeal (K : Type) [CommRing K] : Ideal (Polynomial K) :=
  Ideal.span {Polynomial.X^2}

abbrev Dual (K : Type) [CommRing K] := Polynomial K ⧸ dualIdeal K

/-- The augmentation sends epsilon to zero. -/
def residue (K : Type) [CommRing K] : Dual K →ₐ[K] K where
  toRingHom := Ideal.Quotient.lift (dualIdeal K) (Polynomial.evalRingHom 0) (by
    intro f hf
    have hker : dualIdeal K ≤ RingHom.ker (Polynomial.evalRingHom (0 : K)) := by
      rw [dualIdeal, Ideal.span_singleton_le_iff_mem]
      simp
    exact hker hf)
  commutes' := by intro c; change Polynomial.eval 0 (Polynomial.C c) = c; simp

def dualToBase (K : Type) [CommRing K] :
    Spec (CommRingCat.of (Dual K)) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (Dual K)))

def origin (K : Type) [CommRing K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (Dual K)) :=
  Spec.map (CommRingCat.ofHom (residue K).toRingHom)

/-- The rational-point differential criterion expressed with the standard
dual-number definition of tangent vectors.  Its tangent map is literally
postcomposition by f. -/
def RationalPointDifferentialCriterion : Prop :=
  ∀ (K : Type) [Field K] (X Y : Scheme)
    (sX : X ⟶ Spec (CommRingCat.of K)) (sY : Y ⟶ Spec (CommRingCat.of K))
    (f : X ⟶ Y), f ≫ sY = sX →
    ∀ (x : Spec (CommRingCat.of K) ⟶ X), x ≫ sX = 𝟙 _ →
    Smooth sX → Smooth sY →
    (∀ b : Spec (CommRingCat.of (Dual K)) ⟶ Y,
      b ≫ sY = dualToBase K → origin K ≫ b = x ≫ f →
      ∃ a : Spec (CommRingCat.of (Dual K)) ⟶ X,
        a ≫ sX = dualToBase K ∧ origin K ≫ a = x ∧ a ≫ f = b) →
    ∃ U : X.Opens, Set.range x ⊆ U ∧ Smooth (U.ι ≫ f)

end LeBrunSalamon.DualNumberGeometry

namespace LeBrunSalamon.PublishedInputs.Smoothness

/-- **Published input (exact):** smooth morphisms have the global lifting
property for affine first-order thickenings.  Stacks Project, Lemma37.11.7
(02H6), smooth implies formally smooth, with Definition37.11.1 (02H0).
The surjective ring map with square-zero kernel is precisely the affine
first-order thickening in that definition.  The conclusion is global on
Spec R; the source's proof establishes this by the vanishing of H^1 of the
quasi-coherent torsor module on the affine closed subscheme.
https://stacks.math.columbia.edu/tag/02H6
https://stacks.math.columbia.edu/tag/02H0 -/
theorem smooth_squareZero_lift
    (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (hker : (RingHom.ker φ)^2 = ⊥)
    (X Y : Scheme) (f : X ⟶ Y) (hf : Smooth f)
    (a : Spec (CommRingCat.of S) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ Y)
    (hsquare : a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b) :
    ∃ l : Spec (CommRingCat.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom φ) ≫ l = a ∧ l ≫ f = b := by
  sorry

/-- **Published input (exact rational-point specialization):** EGA IV4,
Theorem17.11.1(d) implies(a), printed pp82--83 (PMIHES1967,volume32).
The structural morphisms are locally of finite presentation because they
are smooth.  The rational points x and x≫f have residue fields K, so the
theorem's residue-field isomorphism hypothesis is satisfied.  Tangent
vectors are the dual-number lifts of Stacks Definition33.16.3; their
canonical map is postcomposition by f.  Smoothness at the image of x is
written as an open source neighborhood on which the restriction is smooth.
No affine, integral, separated, or algebraically closed hypothesis is used.
https://www.numdam.org/item/PMIHES_1967__32__5_0/
https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/EGA/EGAIV.4.pdf
https://stacks.math.columbia.edu/tag/0B28 (Definition33.16.3)
https://stacks.math.columbia.edu/tag/0B2F (canonical tangent-map functoriality) -/
theorem smooth_of_surjective_tangent_lifts
    (K : Type) [Field K] (X Y : Scheme)
    (sX : X ⟶ Spec (CommRingCat.of K)) (sY : Y ⟶ Spec (CommRingCat.of K))
    (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ sX = 𝟙 _)
    (hX : Smooth sX) (hY : Smooth sY)
    (hT : ∀ b : Spec (CommRingCat.of (DualNumberGeometry.Dual K)) ⟶ Y,
      b ≫ sY = DualNumberGeometry.dualToBase K →
      DualNumberGeometry.origin K ≫ b = x ≫ f →
      ∃ a : Spec (CommRingCat.of (DualNumberGeometry.Dual K)) ⟶ X,
        a ≫ sX = DualNumberGeometry.dualToBase K ∧
          DualNumberGeometry.origin K ≫ a = x ∧ a ≫ f = b) :
    ∃ U : X.Opens, Set.range x ⊆ U ∧ Smooth (U.ι ≫ f) := by
  sorry

end LeBrunSalamon.PublishedInputs.Smoothness

end

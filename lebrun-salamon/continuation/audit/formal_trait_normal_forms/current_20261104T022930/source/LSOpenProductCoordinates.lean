import LSAffineProductRing
import LSClosedIdealCoefficients
import LSSectionCover

/-!
The actual open product U × U in X × X, its coordinate-ring comparison, and
the identification of the actual diagonal restriction with multiplication.
All comparisons retain the scheme maps and the given scalar structures.
Candidate outside source/: native verification is pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open scoped TensorProduct

namespace LeBrunSalamon.OpenProductCoordinates

def squareInclusion {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    SelfProduct (U.ι ≫ s) ⟶ SelfProduct s :=
  pullback.map (U.ι ≫ s) (U.ι ≫ s) s s U.ι U.ι (𝟙 ComplexBase)
    (by simp) (by simp)

instance squareInclusion_isOpenImmersion {X : Scheme}
    (s : X ⟶ ComplexBase) (U : X.Opens) : IsOpenImmersion (squareInclusion s U) := by
  dsimp [squareInclusion]
  infer_instance

@[reassoc (attr := simp)] theorem squareInclusion_fst {X : Scheme}
    (s : X ⟶ ComplexBase) (U : X.Opens) :
    squareInclusion s U ≫ firstProjection s = firstProjection (U.ι ≫ s) ≫ U.ι := by
  simp [squareInclusion]

@[reassoc (attr := simp)] theorem squareInclusion_snd {X : Scheme}
    (s : X ⟶ ComplexBase) (U : X.Opens) :
    squareInclusion s U ≫ secondProjection s = secondProjection (U.ι ≫ s) ≫ U.ι := by
  simp [squareInclusion]

def productOpen {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    (SelfProduct s).Opens := (squareInclusion s U).opensRange

theorem productOpen_le_fst {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    productOpen s U ≤ firstProjection s ⁻¹ᵁ U := by
  rintro z ⟨w, rfl⟩
  change (squareInclusion s U ≫ firstProjection s) w ∈ U
  rw [squareInclusion_fst]
  exact (firstProjection (U.ι ≫ s) w).property

theorem productOpen_le_snd {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    productOpen s U ≤ secondProjection s ⁻¹ᵁ U := by
  rintro z ⟨w, rfl⟩
  change (squareInclusion s U ≫ secondProjection s) w ∈ U
  rw [squareInclusion_snd]
  exact (secondProjection (U.ι ≫ s) w).property

theorem productOpen_eq {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    productOpen s U = SectionCoverProof.squareOpen s U := by
  apply le_antisymm
  · exact le_inf (productOpen_le_fst s U) (productOpen_le_snd s U)
  · intro z hz
    let V := SectionCoverProof.squareOpen s U
    have hleft : Set.range (V.ι ≫ firstProjection s) ⊆ Set.range U.ι := by
      rintro _ ⟨w, rfl⟩
      exact ⟨⟨firstProjection s w.val, w.property.1⟩, rfl⟩
    have hright : Set.range (V.ι ≫ secondProjection s) ⊆ Set.range U.ι := by
      rintro _ ⟨w, rfl⟩
      exact ⟨⟨secondProjection s w.val, w.property.2⟩, rfl⟩
    let a := IsOpenImmersion.lift U.ι (V.ι ≫ firstProjection s) hleft
    let b := IsOpenImmersion.lift U.ι (V.ι ≫ secondProjection s) hright
    have ha : a ≫ U.ι = V.ι ≫ firstProjection s := IsOpenImmersion.lift_fac _ _ _
    have hb : b ≫ U.ι = V.ι ≫ secondProjection s := IsOpenImmersion.lift_fac _ _ _
    have hs : a ≫ (U.ι ≫ s) = b ≫ (U.ι ≫ s) := by
      rw [← Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
        Category.assoc, pullback.condition]
    let q : V.toScheme ⟶ SelfProduct (U.ι ≫ s) := pullback.lift a b hs
    have hq : q ≫ squareInclusion s U = V.ι := by
      apply pullback.hom_ext
      · simpa [q, Category.assoc] using ha
      · simpa [q, Category.assoc] using hb
    exact ⟨q ⟨z, hz⟩, congrArg (fun h => h ⟨z, hz⟩) hq⟩

theorem productOpen_isAffine {X : Scheme} (s : X ⟶ ComplexBase)
    (U : X.Opens) (hU : IsAffineOpen U) : IsAffineOpen (productOpen s U) := by
  letI : IsAffine U.toScheme := hU
  exact isAffineOpen_opensRange (squareInclusion s U)

@[reassoc] theorem squareInclusion_diagonal {X : Scheme}
    (s : X ⟶ ComplexBase) (U : X.Opens) :
    diagonal (U.ι ≫ s) ≫ squareInclusion s U = U.ι ≫ diagonal s := by
  apply pullback.hom_ext <;> simp [Category.assoc]

theorem diagonal_preimage_productOpen {X : Scheme}
    (s : X ⟶ ComplexBase) (U : X.Opens) :
    diagonal s ⁻¹ᵁ productOpen s U = U := by
  rw [productOpen_eq]
  ext x
  change (firstProjection s (diagonal s x) ∈ U ∧
    secondProjection s (diagonal s x) ∈ U) ↔ x ∈ U
  have hf := congrArg (fun f => f x) (pullback.diagonal_fst s)
  have hg := congrArg (fun f => f x) (pullback.diagonal_snd s)
  change firstProjection s (diagonal s x) = x at hf
  change secondProjection s (diagonal s x) = x at hg
  rw [hf, hg, and_self]

def Coefficients {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) : Type :=
  RingSections X U

instance coefficientsCommRing {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    CommRing (Coefficients s U) := inferInstanceAs (CommRing (RingSections X U))

instance coefficientsModule {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    Module ℂ (Coefficients s U) := Module.compHom (RingSections X U)
      (KunnethDegreeZero.constants s U)

instance coefficientsAlgebra {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    Algebra ℂ (Coefficients s U) := Algebra.compHom (RingSections X U)
      (KunnethDegreeZero.constants s U)

theorem topIso_inv_restrict {X : Scheme} (U : X.Opens) (a : RingSections X ⊤) :
    U.topIso.inv (X.presheaf.map (homOfLE le_top).op a) = U.ι.appTop a := by
  change (X.presheaf.map (homOfLE le_top).op ≫ U.topIso.inv) a = U.ι.appTop a
  simp only [Scheme.Opens.topIso_inv, ← Functor.map_comp, Scheme.Opens.ι_appTop] <;> rfl

def openTopEquiv {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    Coefficients s U ≃ₐ[ℂ] AffineProductRing.Functions (U.ι ≫ s) where
  toFun a := U.topIso.inv a
  invFun a := U.topIso.hom a
  left_inv a := by
    change (U.topIso.inv ≫ U.topIso.hom) a = a
    rw [Iso.inv_hom_id]
    rfl
  right_inv a := by
    change (U.topIso.hom ≫ U.topIso.inv) a = a
    rw [Iso.hom_inv_id]
    rfl
  map_add' a b := U.topIso.inv.hom.map_add a b
  map_mul' a b := U.topIso.inv.hom.map_mul a b
  commutes' c := by
    change U.topIso.inv (KunnethDegreeZero.constants s U c) =
      KunnethDegreeZero.constants (U.ι ≫ s) ⊤ c
    rw [KunnethDegreeZero.constants_top]
    change U.topIso.inv
      (X.presheaf.map (homOfLE le_top).op
        (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) = _
    rw [topIso_inv_restrict, Scheme.Hom.comp_appTop]
    rfl

def ambientRingEquiv {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    RingSections (SelfProduct (U.ι ≫ s)) ⊤ ≃+*
      RingSections (SelfProduct s) (productOpen s U) where
  toFun a := (IsOpenImmersion.ΓIsoTop (squareInclusion s U)).hom a
  invFun a := (IsOpenImmersion.ΓIsoTop (squareInclusion s U)).inv a
  left_inv a := by
    change ((IsOpenImmersion.ΓIsoTop (squareInclusion s U)).hom ≫
      (IsOpenImmersion.ΓIsoTop (squareInclusion s U)).inv) a = a
    rw [Iso.hom_inv_id]
    rfl
  right_inv a := by
    change ((IsOpenImmersion.ΓIsoTop (squareInclusion s U)).inv ≫
      (IsOpenImmersion.ΓIsoTop (squareInclusion s U)).hom) a = a
    rw [Iso.inv_hom_id]
    rfl
  map_add' a b := (IsOpenImmersion.ΓIsoTop (squareInclusion s U)).hom.hom.map_add a b
  map_mul' a b := (IsOpenImmersion.ΓIsoTop (squareInclusion s U)).hom.hom.map_mul a b

theorem ambientRingEquiv_symm {X : Scheme} (s : X ⟶ ComplexBase)
    (U : X.Opens) (a : RingSections (SelfProduct s) (productOpen s U)) :
    (ambientRingEquiv s U).symm a =
      (squareInclusion s U).appLE (productOpen s U) ⊤
        (by exact (Scheme.Hom.preimage_opensRange (squareInclusion s U)).ge) a := by
  change (IsOpenImmersion.ΓIsoTop (squareInclusion s U)).inv a = _
  congr 1
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.symm_inv,
    Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  rfl

def ringMap {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    (Coefficients s U ⊗[ℂ] Coefficients s U) →+*
      RingSections (SelfProduct s) (productOpen s U) :=
  (ambientRingEquiv s U).toRingHom.comp
    ((AffineProductRing.ringMap (U.ι ≫ s) (U.ι ≫ s)).toRingHom.comp
      (Algebra.TensorProduct.congr (openTopEquiv s U) (openTopEquiv s U)).toRingEquiv.toRingHom)

theorem ringMap_bijective {X : Scheme} (s : X ⟶ ComplexBase) [IsSeparated s]
    (U : X.Opens) (hU : IsAffineOpen U) : Function.Bijective (ringMap s U) := by
  letI : IsAffine U.toScheme := hU
  exact (ambientRingEquiv s U).bijective.comp
    ((AffineProductRing.ringMap_bijective (U.ι ≫ s) (U.ι ≫ s)).comp
      (Algebra.TensorProduct.congr (openTopEquiv s U) (openTopEquiv s U)).bijective)

def ringEquiv {X : Scheme} (s : X ⟶ ComplexBase) [IsSeparated s]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (Coefficients s U ⊗[ℂ] Coefficients s U) ≃+*
      RingSections (SelfProduct s) (productOpen s U) :=
  RingEquiv.ofBijective (ringMap s U) (ringMap_bijective s U hU)

private theorem appLE_top_comp {A B C : Scheme} (f : A ⟶ B) (g : B ⟶ C)
    (U : C.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U) (hfg : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U) :
    (f ≫ g).appLE U ⊤ hfg = g.appLE U ⊤ hg ≫ f.appTop := by
  calc
    _ = g.appLE U ⊤ hg ≫ f.appLE ⊤ ⊤ le_rfl :=
      (Scheme.Hom.appLE_comp_appLE f g U ⊤ ⊤ hg le_rfl).symm
    _ = _ := by simp [Scheme.Hom.appLE]

private theorem open_topIso_inv_eq_appLE {X : Scheme} (U : X.Opens) :
    U.topIso.inv = U.ι.appLE U ⊤ U.ι_preimage_self.ge := by
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE] <;> congr 1

private theorem appLE_eq_of_hom_eq {X Y : Scheme} {f g : X ⟶ Y}
    (e : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

def firstFunctionMap {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    RingSections X U →+* RingSections (SelfProduct s) (productOpen s U) :=
  ((firstProjection s).appLE U (productOpen s U) (productOpen_le_fst s U)).hom

def secondFunctionMap {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    RingSections X U →+* RingSections (SelfProduct s) (productOpen s U) :=
  ((secondProjection s).appLE U (productOpen s U) (productOpen_le_snd s U)).hom

theorem firstFunctionMap_pullback {X : Scheme} (s : X ⟶ ComplexBase)
    (U : X.Opens) (a : RingSections X U) :
    (ambientRingEquiv s U).symm (firstFunctionMap s U a) =
      (firstProjection (U.ι ≫ s)).appTop (U.topIso.inv a) := by
  rw [ambientRingEquiv_symm]
  change (((firstProjection s).appLE U (productOpen s U) (productOpen_le_fst s U)) ≫
    (squareInclusion s U).appLE (productOpen s U) ⊤ _) a = _
  rw [Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_hom_eq (squareInclusion_fst s U) U ⊤ _
      (by intro x _; exact (firstProjection (U.ι ≫ s) x).property),
    appLE_top_comp (firstProjection (U.ι ≫ s)) U.ι U U.ι_preimage_self.ge,
    ← open_topIso_inv_eq_appLE]
  rfl

theorem secondFunctionMap_pullback {X : Scheme} (s : X ⟶ ComplexBase)
    (U : X.Opens) (a : RingSections X U) :
    (ambientRingEquiv s U).symm (secondFunctionMap s U a) =
      (secondProjection (U.ι ≫ s)).appTop (U.topIso.inv a) := by
  rw [ambientRingEquiv_symm]
  change (((secondProjection s).appLE U (productOpen s U) (productOpen_le_snd s U)) ≫
    (squareInclusion s U).appLE (productOpen s U) ⊤ _) a = _
  rw [Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_hom_eq (squareInclusion_snd s U) U ⊤ _
      (by intro x _; exact (secondProjection (U.ι ≫ s) x).property),
    appLE_top_comp (secondProjection (U.ι ≫ s)) U.ι U U.ι_preimage_self.ge,
    ← open_topIso_inv_eq_appLE]
  rfl

theorem ringMap_tmul {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens)
    (a b : Coefficients s U) :
    ringMap s U (a ⊗ₜ[ℂ] b) = firstFunctionMap s U a * secondFunctionMap s U b := by
  apply (ambientRingEquiv s U).symm.injective
  rw [map_mul, firstFunctionMap_pullback, secondFunctionMap_pullback]
  change (ambientRingEquiv s U).symm ((ambientRingEquiv s U)
    (AffineProductRing.ringMap (U.ι ≫ s) (U.ι ≫ s)
      (Algebra.TensorProduct.congr (openTopEquiv s U) (openTopEquiv s U)
        (a ⊗ₜ[ℂ] b)))) = _
  rw [RingEquiv.symm_apply_apply]
  exact AffineProductRing.ringMap_tmul (U.ι ≫ s) (U.ι ≫ s)
    (U.topIso.inv a) (U.topIso.inv b)

def diagonalMap {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    RingSections (SelfProduct s) (productOpen s U) →+* RingSections X U :=
  ((diagonal s).appLE (productOpen s U) U
    (diagonal_preimage_productOpen s U).ge).hom

theorem diagonalMap_first {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens)
    (a : RingSections X U) : diagonalMap s U (firstFunctionMap s U a) = a := by
  change (((firstProjection s).appLE U (productOpen s U) _) ≫
    (diagonal s).appLE (productOpen s U) U _) a = a
  rw [Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_hom_eq (pullback.diagonal_fst s) U U _ le_rfl]
  simp [Scheme.Hom.appLE]
  change (X.presheaf.map (𝟙 (op U))) a = a
  rw [X.presheaf.map_id]
  rfl

theorem diagonalMap_second {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens)
    (a : RingSections X U) : diagonalMap s U (secondFunctionMap s U a) = a := by
  change (((secondProjection s).appLE U (productOpen s U) _) ≫
    (diagonal s).appLE (productOpen s U) U _) a = a
  rw [Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_hom_eq (pullback.diagonal_snd s) U U _ le_rfl]
  simp [Scheme.Hom.appLE]
  change (X.presheaf.map (𝟙 (op U))) a = a
  rw [X.presheaf.map_id]
  rfl

theorem diagonalMap_ringMap {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens)
    (t : Coefficients s U ⊗[ℂ] Coefficients s U) :
    diagonalMap s U (ringMap s U t) = Algebra.TensorProduct.lmul' ℂ t := by
  refine TensorProduct.inductionOn t ?_ ?_
  · intro a b
    rw [ringMap_tmul, map_mul, diagonalMap_first, diagonalMap_second]
    rfl
  · intro a b ha hb
    simp only [map_add, ha, hb]

theorem diagonalMap_eq_zero_iff {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens)
    (a : RingSections (SelfProduct s) (productOpen s U)) :
    diagonalMap s U a = 0 ↔ (diagonal s).app (productOpen s U) a = 0 := by
  let h := (diagonal_preimage_productOpen s U).ge
  have hi : IsIso (homOfLE h) := by
    have he : homOfLE h = eqToHom (diagonal_preimage_productOpen s U).symm :=
      Subsingleton.elim _ _
    rw [he]
    infer_instance
  letI := hi
  have hinj := (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (homOfLE h).op)).injective
  change X.presheaf.map (homOfLE h).op
    ((diagonal s).app (productOpen s U) a) = 0 ↔ _
  constructor
  · intro hzero
    apply hinj
    simpa only [map_zero] using hzero
  · intro hzero
    rw [hzero, map_zero]

theorem diagonalKernel_eq_map {X : Scheme} (s : X ⟶ ComplexBase) [IsSeparated s]
    (U : X.Opens) (hU : IsAffineOpen U) :
    RingHom.ker ((diagonal s).app (productOpen s U)).hom =
      (KaehlerDifferential.ideal ℂ (Coefficients s U)).map (ringMap s U) := by
  apply (Ideal.comap_injective_of_surjective (ringMap s U)
    (ringMap_bijective s U hU).surjective)
  rw [Ideal.comap_map_of_bijective _ (ringMap_bijective s U hU)]
  ext t
  change (diagonal s).app (productOpen s U) (ringMap s U t) = 0 ↔
    Algebra.TensorProduct.lmul' ℂ t = 0
  rw [← diagonalMap_eq_zero_iff, diagonalMap_ringMap]

theorem diagonalPower_quotient_eq_zero_iff {X : Scheme}
    (s : X ⟶ ComplexBase) [IsSeparated s] (U : X.Opens) (hU : IsAffineOpen U)
    (k : ℕ) (t : Coefficients s U ⊗[ℂ] Coefficients s U) :
    Ideal.Quotient.mk ((RingHom.ker ((diagonal s).app (productOpen s U)).hom) ^ k)
      (ringMap s U t) = 0 ↔
    Ideal.Quotient.mk ((KaehlerDifferential.ideal ℂ (Coefficients s U)) ^ k) t = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
    diagonalKernel_eq_map s U hU, ← Ideal.map_pow,
    Ideal.mem_map_iff_of_surjective (ringMap s U) (ringMap_bijective s U hU).surjective]
  constructor
  · rintro ⟨u, hu, hut⟩
    exact (ringMap_bijective s U hU).injective hut ▸ hu
  · intro ht
    exact ⟨t, ht, rfl⟩

end LeBrunSalamon.OpenProductCoordinates

end

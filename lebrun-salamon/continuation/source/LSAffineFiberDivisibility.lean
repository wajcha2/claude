import LSHomVelocity

/-!
# Divisibility from a zero affine fibre

The argument tests a section against the actual quotient of its module of
global sections by the polynomial coordinate.  Both sheaf maps used in the
test are obtained from existing adjunctions.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.AffineFiberDivisibility

/-- A quasicoherent affine sheaf map obtained from its map of global modules. -/
def homOfGlobal {R : CommRingCat} (E N : (Spec R).Modules) [E.IsQuasicoherent]
    (q : (moduleSpecΓFunctor (R := R)).obj E ⟶
      (moduleSpecΓFunctor (R := R)).obj N) : E ⟶ N :=
  (asIso E.fromTildeΓ).inv ≫ (tilde.adjunction.homEquiv _ _).symm q

theorem homOfGlobal_spec {R : CommRingCat} (E N : (Spec R).Modules)
    [E.IsQuasicoherent]
    (q : (moduleSpecΓFunctor (R := R)).obj E ⟶
      (moduleSpecΓFunctor (R := R)).obj N) :
    (moduleSpecΓFunctor (R := R)).map (homOfGlobal E N q) = q := by
  let adj := tilde.adjunction (R := R)
  have h : E.fromTildeΓ ≫ homOfGlobal E N q = (adj.homEquiv _ _).symm q := by
    change (asIso E.fromTildeΓ).hom ≫ (asIso E.fromTildeΓ).inv ≫
      (adj.homEquiv _ _).symm q = _
    rw [Iso.hom_inv_id_assoc]
    rfl
  have h' := congrArg (adj.homEquiv _ _) h
  erw [Equiv.apply_symm_apply, adj.homEquiv_apply, CategoryTheory.Functor.map_comp,
    ← Category.assoc] at h'
  change (adj.unit.app ((moduleSpecΓFunctor (R := R)).obj E) ≫
    (moduleSpecΓFunctor (R := R)).map (adj.counit.app E)) ≫ _ = q at h'
  rw [adj.right_triangle_components] at h'
  exact (Category.id_comp ((moduleSpecΓFunctor (R := R)).map
    (homOfGlobal E N q))).symm.trans h'

/-- A section whose pullback vanishes is killed by every sheaf map into
a pushforward from that source. This is the pullback adjunction itself. -/
theorem map_eq_zero_of_pullSection_zero {Y X : Scheme} (f : Y ⟶ X)
    (E : OModule X) (N : OModule Y) (a : GlobalSections E)
    (ha : pullSection f (sectionFromValue a) = 0)
    (q : E ⟶ (Scheme.Modules.pushforward f).obj N) : q.app ⊤ a = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hz : (adj.unit.app E).app ⊤ a = 0 := by
    have h := congrArg (fun s => sectionValue s) ha
    simpa only [pullSection_value, sectionFromValue_spec, sectionValue_zero] using h
  have hq := (adj.homEquiv _ _).apply_symm_apply q
  rw [adj.homEquiv_apply] at hq
  rw [← hq]
  change ((adj.homEquiv _ _).symm q).app ⊤ ((adj.unit.app E).app ⊤ a) = 0
  rw [hz, map_zero]

namespace PolynomialQuotient

variable (M : Type*) [AddCommGroup M] [Module (Polynomial ℂ) M]

def multiples : Submodule (Polynomial ℂ) M :=
  LinearMap.range (LinearMap.lsmul (Polynomial ℂ) M Polynomial.X)

abbrev Quotient := M ⧸ multiples M

instance : Module ℂ (Quotient M) :=
  Module.compHom (Quotient M) Polynomial.C

theorem X_smul (z : Quotient M) : (Polynomial.X : Polynomial ℂ) • z = 0 := by
  obtain ⟨m, rfl⟩ := (multiples M).mkQ_surjective z
  change (multiples M).mkQ (Polynomial.X • m) = 0
  exact (Submodule.Quotient.mk_eq_zero (multiples M)).mpr ⟨m, rfl⟩

theorem polynomial_smul (r : Polynomial ℂ) (z : Quotient M) :
    r • z = Polynomial.eval 0 r • z := by
  have hd : Polynomial.X ∣ r - Polynomial.C (Polynomial.eval 0 r) := by
    rw [Polynomial.X_dvd_iff]
    simp [Polynomial.coeff_zero_eq_eval_zero]
  obtain ⟨s, hs⟩ := hd
  have hr : r = Polynomial.C (Polynomial.eval 0 r) + Polynomial.X * s := by
    rw [← hs]
    abel
  calc
    r • z = (Polynomial.C (Polynomial.eval 0 r) + Polynomial.X * s) • z :=
      congrArg (fun p : Polynomial ℂ => p • z) hr
    _ = Polynomial.eval 0 r • z := by
      rw [add_smul, mul_smul, X_smul, add_zero]
      rfl

end PolynomialQuotient

abbrev quotientSheaf (M : ModuleCat (CommRingCat.of (Polynomial ℂ))) :
    OModule ComplexBase :=
  tilde (R := CommRingCat.of ℂ)
    (ModuleCat.of (CommRingCat.of ℂ) (PolynomialQuotient.Quotient M))

def quotientFrame (M : ModuleCat (CommRingCat.of (Polynomial ℂ))) :=
  tilde.isoTop (R := CommRingCat.of ℂ)
    (ModuleCat.of (CommRingCat.of ℂ) (PolynomialQuotient.Quotient M))

def quotientTest (M : ModuleCat (CommRingCat.of (Polynomial ℂ))) :
    M ⟶ (moduleSpecΓFunctor (R := CommRingCat.of (Polynomial ℂ))).obj
      ((Scheme.Modules.pushforward (Smoothing.scalarPoint 0)).obj (quotientSheaf M)) :=
  ModuleCat.ofHom (X := M)
    (Y := (moduleSpecΓFunctor (R := CommRingCat.of (Polynomial ℂ))).obj
      ((Scheme.Modules.pushforward (Smoothing.scalarPoint 0)).obj (quotientSheaf M)))
    { toFun := fun (m : M) => (quotientFrame M).hom
        ((PolynomialQuotient.multiples M).mkQ m)
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro r m
        have hm := (PolynomialQuotient.multiples M).mkQ.map_smul r m
        have hr := PolynomialQuotient.polynomial_smul M r
          ((PolynomialQuotient.multiples M).mkQ m)
        have he := (quotientFrame M).hom.hom.map_smul (Polynomial.eval 0 r)
          ((PolynomialQuotient.multiples M).mkQ m)
        have hp : (Smoothing.scalarPoint 0).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv r) =
            (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (Polynomial.eval 0 r) := by
          exact (congrArg (fun h : CommRingCat.of (Polynomial ℂ) ⟶
              Γ(ComplexBase, ⊤) => h r)
            (Scheme.ΓSpecIso_inv_naturality
              (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℂ))))).symm
        change (quotientFrame M).hom ((PolynomialQuotient.multiples M).mkQ (r • m)) =
          (Smoothing.scalarPoint 0).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv r) •
              (show GlobalSections (quotientSheaf M) from
                (quotientFrame M).hom ((PolynomialQuotient.multiples M).mkQ m))
        calc
          _ = (quotientFrame M).hom
              (Polynomial.eval 0 r • (PolynomialQuotient.multiples M).mkQ m) :=
            congrArg (fun z => (quotientFrame M).hom z) (hm.trans hr)
          _ = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (Polynomial.eval 0 r) •
              (show GlobalSections (quotientSheaf M) from
                (quotientFrame M).hom ((PolynomialQuotient.multiples M).mkQ m)) := he
          _ = _ := by rw [hp] }

theorem quotientTest_apply (M : ModuleCat (CommRingCat.of (Polynomial ℂ))) (m : M) :
    quotientTest M m = (quotientFrame M).hom
      ((PolynomialQuotient.multiples M).mkQ m) := rfl

/-- The quotient module supplies a separating test for a section not
divisible by the affine coordinate. -/
theorem affineLine_section_divisible (E : OModule Smoothing.AffineLine)
    [E.IsQuasicoherent] (a : GlobalSections E)
    (ha : pullSection (Smoothing.scalarPoint 0) (sectionFromValue a) = 0) :
    ∃ b : GlobalSections E, a = Smoothing.parameterFunction • b := by
  let R : CommRingCat := CommRingCat.of (Polynomial ℂ)
  let M : ModuleCat R := (moduleSpecΓFunctor (R := R)).obj E
  let N := quotientSheaf M
  let e := quotientFrame M
  let p := Smoothing.scalarPoint 0
  let q : M ⟶ (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward p).obj N) := quotientTest M
  let g := homOfGlobal E ((Scheme.Modules.pushforward p).obj N) q
  have hg : g.app ⊤ a = 0 :=
    map_eq_zero_of_pullSection_zero p E N a ha g
  have hq : q a = 0 := by
    have h := congrArg (fun k : M ⟶ (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward p).obj N) => k a)
      (homOfGlobal_spec E ((Scheme.Modules.pushforward p).obj N) q)
    exact h.symm.trans hg
  have hz : (PolynomialQuotient.multiples M).mkQ a = 0 := by
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    exact (quotientTest_apply M a).symm.trans (hq.trans e.hom.hom.map_zero.symm)
  have hm : a ∈ PolynomialQuotient.multiples M :=
    (Submodule.Quotient.mk_eq_zero (PolynomialQuotient.multiples M)).mp hz
  obtain ⟨b, hb⟩ := hm
  refine ⟨b, ?_⟩
  exact hb.symm

end LeBrunSalamon.AffineFiberDivisibility

end

import RecompileBasePart05B
import LSResidueTensorLift

/-!
The actual degree-zero base-change morphism for an arbitrary commutative
base ring. Scalars are obtained from the supplied scheme maps. The map on
pure tensors is pullback of the supplied section followed by multiplication
by the supplied scalar. In particular its value on a tensor with 1 is the
original `pullSection`, and a surjective residue base-change map lifts the
original finite tuple of algebraic sections.

There is no cohomology theorem and no admission in this file. Off-graph
candidate; the mathematical input giving bijectivity is kept separate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open scoped TensorProduct

namespace LeBrunSalamon.CanonicalSectionBaseChange

variable {R : Type} [CommRing R]

/-- Constants through the actual base morphism, followed by restriction. -/
def constants {X : Scheme} (s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    R →+* RingSections X U :=
  ((X.presheaf.map (homOfLE le_top).op).hom.comp s.appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem constants_top {X : Scheme} (s : X ⟶ Spec (CommRingCat.of R)) (r : R) :
    constants s ⊤ r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
  simp [constants]

theorem constants_naturality {X Y : Scheme} (f : X ⟶ Y)
    (sX : X ⟶ Spec (CommRingCat.of R)) (sY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ sY = sX) (r : R) :
    f.appTop (constants sY ⊤ r) = constants sX ⊤ r := by
  rw [constants_top, constants_top]
  change (sY.appTop ≫ f.appTop) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) = _
  rw [← Scheme.Hom.comp_appTop, hf]

/-- Global sections with the scalar action of the specified base map. -/
def Sections {X : Scheme} (s : X ⟶ Spec (CommRingCat.of R))
    (E : OModule X) : Type _ := GlobalSections E

instance sectionsAddCommGroup {X : Scheme} (s : X ⟶ Spec (CommRingCat.of R))
    (E : OModule X) : AddCommGroup (Sections s E) :=
  inferInstanceAs (AddCommGroup (GlobalSections E))

instance sectionsModule {X : Scheme} (s : X ⟶ Spec (CommRingCat.of R))
    (E : OModule X) : Module R (Sections s E) :=
  Module.compHom (GlobalSections E) (constants s ⊤)

/-- The original section pullback is linear for the actual base action. -/
def pullLinear {X Y : Scheme} (f : X ⟶ Y)
    (sX : X ⟶ Spec (CommRingCat.of R)) (sY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ sY = sX) (E : OModule Y) :
    Sections sY E →ₗ[R] Sections sX (pullbackModule f E) where
  toFun a := sectionValue (pullSection f (sectionFromValue a))
  map_add' := by
    intro a b
    simp only [pullSection_value, sectionFromValue_spec]
    exact map_add (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app ⊤).hom a b
  map_smul' := by
    intro r a
    change GlobalSections E at a
    change sectionValue (pullSection f (sectionFromValue (constants sY ⊤ r • a))) =
      constants sX ⊤ r • sectionValue (pullSection f (sectionFromValue a))
    rw [← constants_naturality f sX sY hf]
    simp only [pullSection_value, sectionFromValue_spec]
    exact Scheme.Modules.Hom.app_smul
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E) (constants sY ⊤ r) a

variable {S : Type} [CommRing S] [Algebra R S]
variable {X Y : Scheme} (sX : X ⟶ Spec (CommRingCat.of R))
  (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of S))
  (h : p ≫ sX = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The two scalar actions agree because the displayed square commutes. -/
theorem constants_baseChange (r : R) :
    constants q ⊤ (algebraMap R S r) = constants (p ≫ sX) ⊤ r := by
  rw [constants_top, constants_top, h, Scheme.Hom.comp_appTop]
  exact congrArg (fun z => q.appTop z)
    (congrArg (fun k : CommRingCat.of R ⟶ Γ(Spec (CommRingCat.of S), ⊤) => k r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S))))

/-- The bilinear map `(a,b) ↦ q*(b) • p*(a)`, with all scalar transports
performed through the original commutative square. -/
def tensorPair (E : OModule X) :
    Sections sX E →ₗ[R] S →ₗ[R] Sections (p ≫ sX) (pullbackModule p E) where
  toFun a :=
    { toFun := fun b => constants q ⊤ b •
        sectionValue (pullSection p (sectionFromValue a))
      map_add' := by
        intro b c
        rw [map_add, add_smul]
      map_smul' := by
        intro r b
        change constants q ⊤ (algebraMap R S r * b) •
            sectionValue (pullSection p (sectionFromValue a)) =
          constants (p ≫ sX) ⊤ r •
            (constants q ⊤ b • sectionValue (pullSection p (sectionFromValue a)))
        rw [map_mul, constants_baseChange sX p q h, mul_smul] }
  map_add' := by
    intro a b
    ext c
    change constants q ⊤ c • (pullLinear p (p ≫ sX) sX rfl E) (a + b) =
      constants q ⊤ c • (pullLinear p (p ≫ sX) sX rfl E) a +
        constants q ⊤ c • (pullLinear p (p ≫ sX) sX rfl E) b
    rw [map_add, smul_add]
  map_smul' := by
    intro r a
    ext b
    change constants q ⊤ b • (pullLinear p (p ≫ sX) sX rfl E) (r • a) =
      constants (p ≫ sX) ⊤ r •
        (constants q ⊤ b • (pullLinear p (p ≫ sX) sX rfl E) a)
    rw [map_smul]
    change constants q ⊤ b •
        (constants (p ≫ sX) ⊤ r • (pullLinear p (p ≫ sX) sX rfl E) a) = _
    exact smul_comm _ _ _

/-- The canonical tensor-to-section base-change morphism. -/
def canonicalMap (E : OModule X) :
    Sections sX E ⊗[R] S →ₗ[R] Sections (p ≫ sX) (pullbackModule p E) :=
  TensorProduct.lift (tensorPair sX p q h E)

theorem canonicalMap_tmul (E : OModule X) (a : Sections sX E) (b : S) :
    canonicalMap sX p q h E (a ⊗ₜ[R] b) =
      constants q ⊤ b • sectionValue (pullSection p (sectionFromValue a)) := by
  rw [canonicalMap, TensorProduct.lift.tmul]
  rfl

/-- The unit normalization retains the original `pullSection` map. -/
theorem canonicalMap_tmul_one (E : OModule X) (a : Sections sX E) :
    canonicalMap sX p q h E (a ⊗ₜ[R] (1 : S)) =
      sectionValue (pullSection p (sectionFromValue a)) := by
  rw [canonicalMap_tmul, map_one, one_smul]

/-- The pure-tensor normalization identifies any stated degree-zero
comparison with this actual map. No arbitrary choice of a section-space
equivalence enters the cohomology adapter. -/
theorem canonicalMap_unique (E : OModule X)
    (β : Sections sX E ⊗[R] S →ₗ[R]
      Sections (p ≫ sX) (pullbackModule p E))
    (hβ : ∀ (a : Sections sX E) (b : S),
      β (a ⊗ₜ[R] b) = constants q ⊤ b •
        sectionValue (pullSection p (sectionFromValue a))) :
    β = canonicalMap sX p q h E := by
  ext a b
  exact (hβ a b).trans (canonicalMap_tmul sX p q h E a b).symm

end LeBrunSalamon.CanonicalSectionBaseChange

namespace LeBrunSalamon.CanonicalSectionBaseChange

variable {R : Type} [CommRing R] [IsLocalRing R]
variable {X Y : Scheme} (sX : X ⟶ Spec (CommRingCat.of R))
  (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  (h : p ≫ sX = q ≫ Spec.map
    (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))

/-- Surjectivity of the canonical residue tensor map gives surjectivity
of the actual pullback on section values. -/
theorem pullValue_surjective (E : OModule X)
    (hb : Function.Surjective (canonicalMap sX p q h E)) :
    Function.Surjective
      (fun a : Sections sX E => sectionValue (pullSection p (sectionFromValue a))) :=
  ResidueTensorLift.residue_restrictionRight_surjective
    (canonicalMap sX p q h E) hb _ (canonicalMap_tmul_one sX p q h E)

/-- Surjectivity for the original algebraic-section morphisms. -/
theorem pullSection_surjective (E : OModule X)
    (hb : Function.Surjective (canonicalMap sX p q h E)) :
    Function.Surjective (pullSection p : AlgebraicSection E →
      AlgebraicSection (pullbackModule p E)) := by
  intro a
  obtain ⟨b, hb⟩ := pullValue_surjective sX p q h E hb (sectionValue a)
  refine ⟨sectionFromValue b, ?_⟩
  exact (sectionValue_bijective (pullbackModule p E)).injective hb

/-- A supplied tuple of the original section morphisms lifts without
altering its length or changing its individual entries. -/
theorem lift_finite_tuple (E : OModule X)
    (hb : Function.Surjective (canonicalMap sX p q h E))
    (n : ℕ) (a : Fin n → AlgebraicSection (pullbackModule p E)) :
    ∃ b : Fin n → AlgebraicSection E, ∀ i, pullSection p (b i) = a i := by
  classical
  choose b hb using fun i : Fin n => pullSection_surjective sX p q h E hb (a i)
  exact ⟨b, hb⟩

end LeBrunSalamon.CanonicalSectionBaseChange

end

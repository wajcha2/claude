import RecompileBasePart05B

/-!
Degree-zero Künneth with the actual canonical map.  The only published input
is the separated, quasi-compact case of Stacks Project, Lemma 33.29.1
(Tag 0BED), in degree zero.  The finite-sum presentation and all project
specializations below are proved.  Candidate kept outside source/ until replay.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open scoped TensorProduct BigOperators

namespace LeBrunSalamon.KunnethDegreeZero

variable {k : Type} [Field k]

/-- Scalars come from the supplied map to Spec k, followed by restriction. -/
def constants {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    k →+* RingSections X U :=
  ((X.presheaf.map (homOfLE le_top).op).hom.comp s.appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem constants_top {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k)) (c : k) :
    constants s ⊤ c = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  simp [constants]

theorem constants_naturality {X Y : Scheme} (f : X ⟶ Y)
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ sY = sX) (c : k) :
    f.appTop (constants sY ⊤ c) = constants sX ⊤ c := by
  rw [constants_top, constants_top]
  change (sY.appTop ≫ f.appTop) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) = _
  rw [← Scheme.Hom.comp_appTop, hf]

/-- Actual global sections, with their specified base-field scalar action. -/
def Sections {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k))
    (E : OModule X) : Type _ := GlobalSections E

instance sectionsAddCommGroup {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k))
    (E : OModule X) : AddCommGroup (Sections s E) :=
  inferInstanceAs (AddCommGroup (GlobalSections E))

instance sectionsModule {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k))
    (E : OModule X) : Module k (Sections s E) :=
  Module.compHom (GlobalSections E) (constants s ⊤)

def pullLinear {X Y : Scheme} (f : X ⟶ Y)
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ sY = sX) (E : OModule Y) :
    Sections sY E →ₗ[k] Sections sX (pullbackModule f E) where
  toFun a := sectionValue (pullSection f (sectionFromValue a))
  map_add' := by
    intro a b
    simp only [pullSection_value, sectionFromValue_spec]
    exact map_add (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app ⊤).hom a b
  map_smul' := by
    intro c a
    change GlobalSections E at a
    change sectionValue (pullSection f (sectionFromValue (constants sY ⊤ c • a))) =
      constants sX ⊤ c • sectionValue (pullSection f (sectionFromValue a))
    rw [← constants_naturality f sX sY hf]
    simp only [pullSection_value, sectionFromValue_spec]
    exact Scheme.Modules.Hom.app_smul
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E) (constants sY ⊤ c) a

def tensorLinear {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k)) (E F : OModule X) :
    Sections s E →ₗ[k] Sections s F →ₗ[k] Sections s (tensorSheaf E F) where
  toFun a :=
    { toFun := fun b => (tensorPresentation E F).pair.apply ⊤ a b
      map_add' := by intro b c; exact map_add _ _ _
      map_smul' := by
        intro c b
        exact ((tensorPresentation E F).pair.apply ⊤ a).map_smul (constants s ⊤ c) b }
  map_add' := by
    intro a b
    ext c
    exact congrArg (fun q => q c) (((tensorPresentation E F).pair.apply ⊤).map_add a b)
  map_smul' := by
    intro c a
    ext b
    exact congrArg (fun q => q b)
      (((tensorPresentation E F).pair.apply ⊤).map_smul (constants s ⊤ c) a)

/-- The actual external tensor product for two independently supplied schemes. -/
def externalTensor {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (E : OModule X) (F : OModule Y) : OModule (pullback sX sY) :=
  tensorSheaf (pullbackModule (pullback.fst sX sY) E)
    (pullbackModule (pullback.snd sX sY) F)

def productLinear {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (E : OModule X) (F : OModule Y) :
    Sections sX E →ₗ[k] Sections sY F →ₗ[k]
      Sections (pullback.fst sX sY ≫ sX) (externalTensor sX sY E F) :=
  (tensorLinear (pullback.fst sX sY ≫ sX)
    (pullbackModule (pullback.fst sX sY) E) (pullbackModule (pullback.snd sX sY) F)
    ).compl₁₂
      (pullLinear (pullback.fst sX sY) (pullback.fst sX sY ≫ sX) sX rfl E)
      (pullLinear (pullback.snd sX sY) (pullback.fst sX sY ≫ sX) sY
        (by exact (pullback.condition (f := sX) (g := sY)).symm) F)

/-- Pullback of each section followed by the actual tensor pairing. -/
def canonicalMap {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (E : OModule X) (F : OModule Y) :
    (Sections sX E ⊗[k] Sections sY F) →ₗ[k]
      Sections (pullback.fst sX sY ≫ sX) (externalTensor sX sY E F) :=
  TensorProduct.lift (productLinear sX sY E F)

theorem canonicalMap_tmul {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (E : OModule X) (F : OModule Y) (a : Sections sX E) (b : Sections sY F) :
    canonicalMap sX sY E F (a ⊗ₜ[k] b) =
      sectionValue (tensorSection
        (pullSection (pullback.fst sX sY) (sectionFromValue a))
        (pullSection (pullback.snd sX sY) (sectionFromValue b))) := by
  rw [canonicalMap, TensorProduct.lift.tmul]
  simp only [sectionValue_tensorSection]
  rfl

end LeBrunSalamon.KunnethDegreeZero

namespace LeBrunSalamon.PublishedInputs.Kunneth

/-- Stacks Project, Lemma 33.29.1 (Tag 0BED), n=0, in its explicitly stated
quasi-compact separated case.  The two factors and the quasi-coherent sheaves
are arbitrary; the morphism is the pullback/cup-product map of the source,
normalized on pure tensors by `KunnethDegreeZero.canonicalMap_tmul`.
https://stacks.math.columbia.edu/tag/0BED -/
theorem canonicalMap_bijective {k : Type} [Field k] {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] [IsSeparated sX] [IsSeparated sY]
    (E : OModule X) (F : OModule Y) [E.IsQuasicoherent] [F.IsQuasicoherent] :
    Function.Bijective (KunnethDegreeZero.canonicalMap sX sY E F) := by
  sorry

end LeBrunSalamon.PublishedInputs.Kunneth

namespace LeBrunSalamon.KunnethDegreeZero

/-- The original rank witness really supplies quasi-coherence. -/
theorem quasicoherent_of_locallyFreeRank {X : Scheme} {E : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) : E.IsQuasicoherent := by
  obtain ⟨q, hq, _⟩ := hE
  letI := hq
  letI : E.IsLocallyFree := q.isLocallyFree
  infer_instance

/-- Finite pure-tensor expansion is algebra, not a further geometric input. -/
theorem exists_fin_tmul {k M N : Type*} [CommRing k]
    [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    (t : M ⊗[k] N) :
    ∃ (n : ℕ) (a : Fin n → M) (b : Fin n → N), t = ∑ i, a i ⊗ₜ[k] b i := by
  classical
  have ht : t ∈ Submodule.span k {z : M ⊗[k] N | ∃ a b, a ⊗ₜ[k] b = z} := by
    rw [TensorProduct.span_tmul_eq_top]
    trivial
  obtain ⟨n, c, z, hz⟩ := Submodule.mem_span_set'.1 ht
  choose a b hab using fun i : Fin n => (z i).property
  refine ⟨n, fun i => c i • a i, b, ?_⟩
  rw [← hz]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hab i, TensorProduct.smul_tmul']

/-- Specialization to the two actual line sheaves; all source hypotheses are
derived from properness and the existing finite local frames. -/
theorem lineMap_bijective {d : ℕ} (X : SmoothProperComplexVariety d)
    (L M : LineBundle X.scheme) :
    Function.Bijective (canonicalMap X.structureMap X.structureMap L.sheaf M.sheaf) := by
  letI : CompactSpace X.scheme :=
    QuasiCompact.compactSpace_of_compactSpace X.structureMap
  letI : L.sheaf.IsQuasicoherent := quasicoherent_of_locallyFreeRank L.locallyFree
  letI : M.sheaf.IsQuasicoherent := quasicoherent_of_locallyFreeRank M.locallyFree
  exact PublishedInputs.Kunneth.canonicalMap_bijective
    X.structureMap X.structureMap L.sheaf M.sheaf

/-- The finite external-product sum is obtained from surjectivity and the
proved finite tensor expansion, using the unchanged section equivalence. -/
theorem externalSection_finiteSum {d : ℕ} (X : SmoothProperComplexVariety d)
    (L M : LineBundle X.scheme)
    (B : AlgebraicSection
      (PhaseTwentyEight.externalTensor X.structureMap L.sheaf M.sheaf)) :
    ∃ (n : ℕ) (a : Fin n → AlgebraicSection L.sheaf)
      (b : Fin n → AlgebraicSection M.sheaf),
      B = ∑ i, externalProductSection X.structureMap (a i) (b i) := by
  classical
  obtain ⟨t, ht⟩ := (lineMap_bijective X L M).surjective (sectionValue B)
  obtain ⟨n, a, b, htensor⟩ := exists_fin_tmul t
  refine ⟨n, fun i => sectionFromValue (a i), fun i => sectionFromValue (b i), ?_⟩
  apply (sectionValue_bijective _).injective
  change sectionValue B = (sectionAddEquiv _)
    (∑ i, externalProductSection X.structureMap (sectionFromValue (a i))
      (sectionFromValue (b i)))
  rw [map_sum, ← ht, htensor, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact canonicalMap_tmul X.structureMap X.structureMap L.sheaf M.sheaf (a i) (b i)

end LeBrunSalamon.KunnethDegreeZero

end

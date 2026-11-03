import RecompileExtensionsPart03

/-!
## Proper integral sources and the contact value along a free line

Global functions are proved constant using Mathlib's integral global-function
theorem and algebraic closedness of C. The resulting section descent is used
only for an actually trivial quotient. No claim of descent for an arbitrary
section under a proper surjection is made here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped BigOperators
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.Descent.ProperSections

/-- The actual complex-constant map is bijective on a proper integral
complex scheme. No rational point of its generic fibre is needed. -/
theorem constants_bijective {T : Scheme} [IsIntegral T]
    (sT : T ⟶ ComplexBase) [IsProper sT] :
    Function.Bijective (complexConstants sT) := by
  letI : IsDomain (Scheme.Γ.obj (op T)) :=
    inferInstanceAs (IsDomain Γ(T, ⊤))
  let F : CommRingCat.of ℂ ⟶ Scheme.Γ.obj (op T) :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ sT.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed sT
  have hconst : complexConstants sT = F.hom := by
    ext c
    exact complexConstants_apply_top sT c
  rw [hconst]
  exact IsAlgClosed.ringHom_bijective_of_isIntegral F.hom hF

/-- A scalar section after pullback from any complex base is the pullback
of an actual constant section when its source is proper and integral. -/
theorem unit_pullSection_surjective {T Y : Scheme} [IsIntegral T]
    (f : T ⟶ Y) (sY : Y ⟶ ComplexBase) [IsProper (f ≫ sY)] :
    Function.Surjective (fun a : AlgebraicSection (structureModule Y) =>
      pullSection f a) := by
  intro t
  obtain ⟨c, hc⟩ := (constants_bijective (f ≫ sY)).surjective
    (sectionValue (t ≫ (unitPullbackIso f).hom))
  let s : AlgebraicSection (structureModule Y) :=
    sectionFromValue (complexConstants sY c)
  refine ⟨s, ?_⟩
  apply (cancel_mono (unitPullbackIso f).hom).mp
  apply (sectionValue_bijective _).injective
  change sectionValue (pullSection f s ≫ unitPullbackMap f) =
    sectionValue (t ≫ (unitPullbackIso f).hom)
  calc
    _ = f.appTop (sectionValue s) :=
      (sectionValue_comp (pullSection f s) (unitPullbackMap f)).trans
        (FrameEvaluation.unit_pullSection_value f s)
    _ = f.appTop (complexConstants sY c) :=
      congrArg (fun v : RingSections Y ⊤ => f.appTop v)
        (sectionFromValue_spec (E := structureModule Y) (complexConstants sY c))
    _ = complexConstants (f ≫ sY) c :=
      complexConstants_naturality f (f ≫ sY) sY rfl c
    _ = _ := hc

/-- The same assertion with the original pulled-back-unit convention. -/
theorem unit_restrictSection_surjective {T Y : Scheme} [IsIntegral T]
    (f : T ⟶ Y) (sY : Y ⟶ ComplexBase) [IsProper (f ≫ sY)] :
    Function.Surjective (fun a : AlgebraicSection (structureModule Y) =>
      restrictSection f a) := by
  intro t
  obtain ⟨a, ha⟩ := unit_pullSection_surjective f sY
    ((unitPullbackIso f).inv ≫ t)
  refine ⟨a, ?_⟩
  change pullSection f a = (unitPullbackIso f).inv ≫ t at ha
  change (Scheme.Modules.pullback f).map a = t
  calc
    _ = unitPullbackMap f ≫ pullSection f a :=
      (unitPullbackMap_pullSection f a).symm
    _ = unitPullbackMap f ≫ ((unitPullbackIso f).inv ≫ t) :=
      congrArg (fun s : AlgebraicSection (pullbackModule f (structureModule Y)) =>
        unitPullbackMap f ≫ s) ha
    _ = t := by
      change (unitPullbackIso f).hom ≫ (unitPullbackIso f).inv ≫ t = t
      simp only [Iso.hom_inv_id_assoc]

/-- Surjectivity is transported by the actual image of a sheaf
isomorphism, without replacing the pullback functor by an unrelated model. -/
theorem restrictSection_surjective_of_iso {T Y : Scheme} (f : T ⟶ Y)
    {E F : OModule Y} (e : E ≅ F)
    (hE : Function.Surjective (fun a : AlgebraicSection E => restrictSection f a)) :
    Function.Surjective (fun a : AlgebraicSection F => restrictSection f a) := by
  intro t
  obtain ⟨a, ha⟩ := hE (t ≫ (Scheme.Modules.pullback f).map e.inv)
  refine ⟨a ≫ e.hom, ?_⟩
  change (Scheme.Modules.pullback f).map a =
    t ≫ (Scheme.Modules.pullback f).map e.inv at ha
  change (Scheme.Modules.pullback f).map (a ≫ e.hom) = t
  rw [Functor.map_comp, ha, Category.assoc, ← Functor.map_comp, e.inv_hom_id]
  exact (congrArg
    (fun h : (Scheme.Modules.pullback f).obj F ⟶ (Scheme.Modules.pullback f).obj F =>
      t ≫ h)
    ((Scheme.Modules.pullback f).map_id F)).trans (Category.comp_id t)

/-- Finite reconstruction from the actual coproduct projections. -/
theorem restrictSection_surjective_coproduct {T Y : Scheme} (f : T ⟶ Y)
    {I : Type} [Fintype I] (E : I → OModule Y)
    (h : ∀ i, Function.Surjective (fun a : AlgebraicSection (E i) =>
      restrictSection f a)) :
    Function.Surjective (fun a : AlgebraicSection (∐ E) => restrictSection f a) := by
  classical
  intro t
  choose a ha using fun i => h i (t ≫ (Scheme.Modules.pullback f).map (Sigma.π E i))
  refine ⟨∑ i, a i ≫ Sigma.ι E i, ?_⟩
  exact DirectSumEvaluation.map_coproduct_sum_eq
    (Scheme.Modules.pullback f) (structureModule Y) E a t ha

/-- Every section of the pullback of an actual trivialized finite sum
descends. Properness and integrality belong to the source, not the base. -/
theorem trivial_restrictSection_surjective {T Y : Scheme} [IsIntegral T]
    (f : T ⟶ Y) (sY : Y ⟶ ComplexBase) [IsProper (f ≫ sY)]
    {I : Type} [Fintype I] {E : OModule Y}
    (e : E ≅ ∐ (fun _ : I => structureModule Y)) :
    Function.Surjective (fun a : AlgebraicSection E => restrictSection f a) := by
  apply restrictSection_surjective_of_iso f e.symm
  exact restrictSection_surjective_coproduct f
    (fun _ : I => structureModule Y) (fun _ => unit_restrictSection_surjective f sY)

theorem trivial_pullSection_surjective {T Y : Scheme} [IsIntegral T]
    (f : T ⟶ Y) (sY : Y ⟶ ComplexBase) [IsProper (f ≫ sY)]
    {I : Type} [Fintype I] {E : OModule Y}
    (e : E ≅ ∐ (fun _ : I => structureModule Y)) :
    Function.Surjective (fun a : AlgebraicSection E => pullSection f a) := by
  intro t
  obtain ⟨a, ha⟩ := trivial_restrictSection_surjective f sY e
    ((unitPullbackIso f).hom ≫ t)
  refine ⟨a, ?_⟩
  change restrictSection f a = (unitPullbackIso f).hom ≫ t at ha
  change (unitPullbackIso f).inv ≫ restrictSection f a = t
  exact (congrArg (fun s => (unitPullbackIso f).inv ≫ s) ha).trans
    (by simp only [Iso.inv_hom_id_assoc])

/-- The ordinary quotient argument: a map factoring through an actual
trivial quotient sends every pulled-back section to a descended section.
The factorization is an equality of sheaf morphisms. -/
theorem value_descends_through_trivial_quotient {T Y : Scheme} [IsIntegral T]
    (f : T ⟶ Y) (sY : Y ⟶ ComplexBase) [IsProper (f ≫ sY)]
    {I : Type} [Fintype I] {E Q L : OModule Y}
    (q : E ⟶ Q) (a : Q ⟶ L) (theta : E ⟶ L)
    (hfactor : q ≫ a = theta) (e : Q ≅ ∐ (fun _ : I => structureModule Y))
    (v : AlgebraicSection (pullbackModule f E)) :
    ∃ b : AlgebraicSection L,
      pullSection f b = v ≫ (Scheme.Modules.pullback f).map theta := by
  obtain ⟨w, hw⟩ := trivial_pullSection_surjective f sY e
    (v ≫ (Scheme.Modules.pullback f).map q)
  refine ⟨w ≫ a, ?_⟩
  change pullSection f w = v ≫ (Scheme.Modules.pullback f).map q at hw
  calc
    _ = pullSection f w ≫ (Scheme.Modules.pullback f).map a :=
      pullSection_naturality f w a
    _ = (v ≫ (Scheme.Modules.pullback f).map q) ≫
        (Scheme.Modules.pullback f).map a :=
      congrArg (fun s : AlgebraicSection (pullbackModule f Q) =>
        s ≫ (Scheme.Modules.pullback f).map a) hw
    _ = _ := by rw [Category.assoc, ← Functor.map_comp, hfactor]

/-- Tensoring with an actually trivialized constant factor preserves
the quotient argument, with the tensor maps in their original order. -/
theorem tensor_right_value_descends {T Y : Scheme} [IsIntegral T]
    (f : T ⟶ Y) (sY : Y ⟶ ComplexBase) [IsProper (f ≫ sY)]
    {I : Type} [Fintype I] {E Q L K : OModule Y}
    (q : E ⟶ Q) (a : Q ⟶ L) (theta : E ⟶ L)
    (hfactor : q ≫ a = theta) (e : Q ≅ ∐ (fun _ : I => structureModule Y))
    (k : K ≅ structureModule Y)
    (v : AlgebraicSection (pullbackModule f (tensorSheaf E K))) :
    ∃ b : AlgebraicSection (tensorSheaf L K),
      pullSection f b = v ≫ (Scheme.Modules.pullback f).map
        (tensorMap theta (𝟙 K)) := by
  apply value_descends_through_trivial_quotient f sY
    (tensorMap q (𝟙 K)) (tensorMap a (𝟙 K)) (tensorMap theta (𝟙 K))
    ?_ (tensorIso e k ≪≫ TensorConstruction.rightUnitIso _) v
  rw [← tensorMap_comp, hfactor, Category.id_comp]

theorem tensor_left_value_descends {T Y : Scheme} [IsIntegral T]
    (f : T ⟶ Y) (sY : Y ⟶ ComplexBase) [IsProper (f ≫ sY)]
    {I : Type} [Fintype I] {E Q L K : OModule Y}
    (q : E ⟶ Q) (a : Q ⟶ L) (theta : E ⟶ L)
    (hfactor : q ≫ a = theta) (e : Q ≅ ∐ (fun _ : I => structureModule Y))
    (k : K ≅ structureModule Y)
    (v : AlgebraicSection (pullbackModule f (tensorSheaf K E))) :
    ∃ b : AlgebraicSection (tensorSheaf K L),
      pullSection f b = v ≫ (Scheme.Modules.pullback f).map
        (tensorMap (𝟙 K) theta) := by
  apply value_descends_through_trivial_quotient f sY
    (tensorMap (𝟙 K) q) (tensorMap (𝟙 K) a) (tensorMap (𝟙 K) theta)
    ?_ (tensorIso k e ≪≫ TensorConstruction.leftUnitIso _) v
  rw [← tensorMap_comp, hfactor, Category.id_comp]

end LeBrunSalamon.Construction.Descent.ProperSections

namespace LeBrunSalamon.Construction.Descent.LineContactQuotient

open LeBrunSalamon.Construction.Lines

/-- The contact map on the actual degree-zero quotient of a free line. -/
def contactMap {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (PositivePart.freeLineZeroBundle f).sheaf ⟶ (ContactPositive.contactLine f).sheaf :=
  PositivePart.zeroSection P marking (PositivePart.freeLineProfile f)
    (PositivePart.freeLineSplitting f) ≫ ContactPositive.contactProjection f

/-- The positive part is killed by the actual contact projection; the
splitting identity therefore gives its factorization through the quotient. -/
theorem factorization {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    PositivePart.freeLineZeroProjection f ≫ contactMap f =
      ContactPositive.contactProjection f := by
  have h := congrArg
    (fun a : (PositivePart.freeLineBundle f).sheaf ⟶ (PositivePart.freeLineBundle f).sheaf =>
      a ≫ ContactPositive.contactProjection f)
    (PositivePart.split_total P marking (PositivePart.freeLineProfile f)
      (PositivePart.freeLineSplitting f) (PositivePart.freeLineProfile_nonnegative f))
  change (PositivePart.positiveRetraction P marking (PositivePart.freeLineProfile f)
      (PositivePart.freeLineSplitting f) ≫ PositivePart.freeLinePositiveInclusion f +
      PositivePart.freeLineZeroProjection f ≫
        PositivePart.zeroSection P marking (PositivePart.freeLineProfile f)
          (PositivePart.freeLineSplitting f)) ≫ ContactPositive.contactProjection f = _ at h
  simpa only [Preadditive.add_comp, Category.assoc, ContactPositive.positiveHorizontal,
    comp_zero, zero_add, Category.id_comp, contactMap] using h

/-- Every proper integral source over the line has a descended contact
value. The statement retains the original pulled-back tangent bundle and
contact map, rather than just a splitting profile or numerical degree. -/
theorem component_contact_value {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) {T : Scheme} [IsIntegral T]
    (pi : T ⟶ ProjectiveLine) [IsProper (pi ≫ P.structureMap)]
    (v : AlgebraicSection (pullbackModule pi (PositivePart.freeLineBundle f).sheaf)) :
    ∃ b : AlgebraicSection (ContactPositive.contactLine f).sheaf,
      pullSection pi b = v ≫ (Scheme.Modules.pullback pi).map
        (ContactPositive.contactProjection f) := by
  exact ProperSections.value_descends_through_trivial_quotient pi P.structureMap
    (PositivePart.freeLineZeroProjection f) (contactMap f)
    (ContactPositive.contactProjection f) (factorization f)
    (PositivePart.freeLineZeroTrivialization f) v

theorem component_contact_value_right {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) {T : Scheme} [IsIntegral T]
    (pi : T ⟶ ProjectiveLine) [IsProper (pi ≫ P.structureMap)]
    {K : OModule ProjectiveLine} (k : K ≅ structureModule ProjectiveLine)
    (v : AlgebraicSection (pullbackModule pi
      (tensorSheaf (PositivePart.freeLineBundle f).sheaf K))) :
    ∃ b : AlgebraicSection (tensorSheaf (ContactPositive.contactLine f).sheaf K),
      pullSection pi b = v ≫ (Scheme.Modules.pullback pi).map
        (tensorMap (ContactPositive.contactProjection f) (𝟙 K)) := by
  exact ProperSections.tensor_right_value_descends pi P.structureMap
    (PositivePart.freeLineZeroProjection f) (contactMap f)
    (ContactPositive.contactProjection f) (factorization f)
    (PositivePart.freeLineZeroTrivialization f) k v

theorem component_contact_value_left {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) {T : Scheme} [IsIntegral T]
    (pi : T ⟶ ProjectiveLine) [IsProper (pi ≫ P.structureMap)]
    {K : OModule ProjectiveLine} (k : K ≅ structureModule ProjectiveLine)
    (v : AlgebraicSection (pullbackModule pi
      (tensorSheaf K (PositivePart.freeLineBundle f).sheaf))) :
    ∃ b : AlgebraicSection (tensorSheaf K (ContactPositive.contactLine f).sheaf),
      pullSection pi b = v ≫ (Scheme.Modules.pullback pi).map
        (tensorMap (𝟙 K) (ContactPositive.contactProjection f)) := by
  exact ProperSections.tensor_left_value_descends pi P.structureMap
    (PositivePart.freeLineZeroProjection f) (contactMap f)
    (ContactPositive.contactProjection f) (factorization f)
    (PositivePart.freeLineZeroTrivialization f) k v

end LeBrunSalamon.Construction.Descent.LineContactQuotient

end

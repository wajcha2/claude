import RecompileBasePart05C

/-!
Pullback of the actual nonvanishing open, proved from local line frames.
The scalar criterion uses the existing basic-open/unit lemmas for schemes;
no published input or project geometry admission is introduced.
Candidate kept outside source/ pending native verification.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.NonvanishingPullbackProof

def unitCoefficient {X : Scheme} (a : structureModule X ⟶ structureModule X) :
    RingSections X ⊤ := sectionValue a

@[simp] theorem unitCoefficient_fromValue {X : Scheme} (a : RingSections X ⊤) :
    unitCoefficient (sectionFromValue (E := structureModule X) a) = a :=
  sectionFromValue_spec (E := structureModule X) a

theorem unitEnd_value_comp {X : Scheme}
    (a b : structureModule X ⟶ structureModule X) :
    unitCoefficient (a ≫ b) = unitCoefficient a * unitCoefficient b := by
  let bR : RingSections X ⊤ →ₗ[RingSections X ⊤] RingSections X ⊤ := (b.app ⊤).hom
  change bR (unitCoefficient a) = unitCoefficient a * bR 1
  simpa only [smul_eq_mul, mul_one] using
    bR.map_smul (unitCoefficient a) (1 : RingSections X ⊤)

/-- An endomorphism of the actual unit sheaf is invertible precisely when
its global coefficient is a unit. -/
theorem unitEnd_isIso_iff {X : Scheme}
    (a : structureModule X ⟶ structureModule X) :
    IsIso a ↔ IsUnit (unitCoefficient a) := by
  constructor
  · intro ha
    letI := ha
    apply IsUnit.of_mul_eq_one (unitCoefficient (inv a))
    rw [← unitEnd_value_comp, IsIso.hom_inv_id]
    rfl
  · rintro ⟨u, hu⟩
    let b : structureModule X ⟶ structureModule X :=
      sectionFromValue (E := structureModule X) ((↑(u⁻¹)) : RingSections X ⊤)
    refine ⟨b, ?_, ?_⟩
    · apply (sectionValue_bijective (structureModule X)).injective
      change unitCoefficient (a ≫ b) = 1
      rw [unitEnd_value_comp]
      change unitCoefficient a * unitCoefficient
        (sectionFromValue (E := structureModule X) ((↑(u⁻¹)) : RingSections X ⊤)) = 1
      rw [unitCoefficient_fromValue, ← hu]
      exact Units.mul_inv u
    · apply (sectionValue_bijective (structureModule X)).injective
      change unitCoefficient (b ≫ a) = 1
      rw [unitEnd_value_comp]
      change unitCoefficient
        (sectionFromValue (E := structureModule X) ((↑(u⁻¹)) : RingSections X ⊤)) *
          unitCoefficient a = 1
      rw [unitCoefficient_fromValue, ← hu]
      exact Units.inv_mul u

def unitEndPullback {X Y : Scheme} (f : X ⟶ Y)
    (a : structureModule Y ⟶ structureModule Y) :
    structureModule X ⟶ structureModule X :=
  pullSection f a ≫ unitPullbackMap f

theorem unitEndPullback_value {X Y : Scheme} (f : X ⟶ Y)
    (a : structureModule Y ⟶ structureModule Y) :
    unitCoefficient (unitEndPullback f a) = f.appTop (unitCoefficient a) := by
  have h := unitPullbackMap_adjoint f
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_apply] at h
  have hv := congrArg (fun q => q.app ⊤ (unitCoefficient a)) h
  change (unitPullbackMap f).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (structureModule Y)).app ⊤ (unitCoefficient a)) = f.appTop (unitCoefficient a) at hv
  change (unitPullbackMap f).app ⊤ (sectionValue (pullSection f a)) = _
  rw [pullSection_value]
  exact hv

theorem unitEndPullback_isIso_iff {X Y : Scheme} (f : X ⟶ Y)
    (a : structureModule Y ⟶ structureModule Y) :
    IsIso (unitEndPullback f a) ↔ IsIso ((Scheme.Modules.pullback f).map a) := by
  letI := unitPullbackMap_isIso f
  change IsIso ((unitPullbackIso f).inv ≫
    (Scheme.Modules.pullback f).map a ≫ unitPullbackMap f) ↔ _
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

set_option maxHeartbeats 200000 in
theorem unitEnd_pullback_isIso_iff {X Y : Scheme} (f : X ⟶ Y)
    (a : structureModule Y ⟶ structureModule Y) :
    IsIso ((Scheme.Modules.pullback f).map a) ↔
      IsUnit (f.appTop (unitCoefficient a)) := by
  constructor
  · intro h
    have hi : IsIso (unitEndPullback f a) :=
      (@unitEndPullback_isIso_iff X Y f a).mpr h
    have hu : IsUnit (unitCoefficient (unitEndPullback f a)) :=
      (@unitEnd_isIso_iff X (unitEndPullback f a)).mp hi
    rwa [unitEndPullback_value] at hu
  · intro h
    have hu : IsUnit (unitCoefficient (unitEndPullback f a)) := by
      rw [unitEndPullback_value]
      exact h
    have hi : IsIso (unitEndPullback f a) :=
      (@unitEnd_isIso_iff X (unitEndPullback f a)).mpr hu
    exact (@unitEndPullback_isIso_iff X Y f a).mp hi

theorem isUnit_iff_basicOpen_top {X : Scheme} (a : RingSections X ⊤) :
    IsUnit a ↔ X.basicOpen a = ⊤ := by
  constructor
  · exact X.toRingedSpace.basicOpen_of_isUnit
  · intro h
    apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ a
    intro x hx
    apply (X.toRingedSpace.mem_basicOpen a x hx).mp
    change x ∈ X.basicOpen a
    rw [h]
    trivial

theorem appTop_unit_on_basicOpen {X : Scheme} (a : RingSections X ⊤) :
    IsUnit ((X.basicOpen a).ι.appTop a) := by
  apply (isUnit_iff_basicOpen_top _).mpr
  rw [← Scheme.preimage_basicOpen_top]
  ext x
  exact iff_true_intro x.property

/-- The local-ring condition is already encoded in the basic-open pullback
identity; no flatness or dominance hypothesis is used. -/
theorem image_mem_basicOpen_of_pullback_isIso {X Y : Scheme} (f : X ⟶ Y)
    (a : structureModule Y ⟶ structureModule Y)
    (h : IsIso ((Scheme.Modules.pullback f).map a)) (x : X) :
    f x ∈ Y.basicOpen (unitCoefficient a) := by
  have hu := (unitEnd_pullback_isIso_iff f a).mp h
  have hopen : f ⁻¹ᵁ Y.basicOpen (unitCoefficient a) = ⊤ := by
    rw [Scheme.preimage_basicOpen_top]
    exact (isUnit_iff_basicOpen_top _).mp hu
  change x ∈ f ⁻¹ᵁ Y.basicOpen (unitCoefficient a)
  rw [hopen]
  trivial

theorem pullback_comp_isIso_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E F : OModule Z} (a : E ⟶ F) :
    IsIso ((Scheme.Modules.pullback (f ≫ g)).map a) ↔
      IsIso ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map a)) :=
  (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp f g) a).symm

theorem pullback_pullSection_isIso_iff {X Y Z : Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) {E : OModule Z} (s : AlgebraicSection E) :
    IsIso ((Scheme.Modules.pullback f).map (pullSection g s)) ↔
      IsIso ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s)) := by
  change IsIso ((Scheme.Modules.pullback f).map
    ((unitPullbackIso g).inv ≫ (Scheme.Modules.pullback g).map s)) ↔ _
  rw [Functor.map_comp]
  exact isIso_comp_left_iff _ _

/-- Any open immersion on which the section is an isomorphism contributes
its actual image to the supremum defining the nonvanishing open. -/
theorem image_mem_nonvanishing_of_open_isIso {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] (L : LineBundle Y) (s : AlgebraicSection L.sheaf)
    (h : IsIso ((Scheme.Modules.pullback f).map s)) (x : X) :
    f x ∈ nonvanishingOpen L s := by
  let U : Y.Opens := f.opensRange
  have hrange : Set.range U.ι ⊆ Set.range f := by
    rintro _ ⟨z, rfl⟩
    exact z.property
  let g := IsOpenImmersion.lift f U.ι hrange
  have hg : g ≫ f = U.ι := IsOpenImmersion.lift_fac f U.ι hrange
  have hU : IsIso (restrictSection U.ι s) := by
    change IsIso ((Scheme.Modules.pullback U.ι).map s)
    rw [← hg]
    apply (pullback_comp_isIso_iff g f s).mpr
    letI := h
    infer_instance
  exact TopologicalSpace.Opens.mem_sSup.mpr ⟨U, hU, ⟨x, rfl⟩⟩

theorem exists_local_line_frame {Y : Scheme} (L : LineBundle Y) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ Nonempty
      (structureModule U.toScheme ≅ pullbackModule U.ι L.sheaf) := by
  obtain ⟨q, hq, hr⟩ := L.locallyFree
  letI := hq
  obtain ⟨i, hi⟩ := ((_root_.Opens.coversTop_iff Y q.X).mp q.coversTop).exists_mem y
  refine ⟨q.X i, hi, ⟨?_⟩⟩
  exact (coproductUniqueIso (fun _ : Fin 1 =>
    structureModule (Scheme.Opens.toScheme (X := Y) (q.X i)))).symm ≪≫
    DominantSectionInjectivityProof.localFreePullbackIso q hr i

theorem nonvanishingOpen_pullback {X Y : Scheme} (f : X ⟶ Y)
    (L : LineBundle Y) (s : AlgebraicSection L.sheaf) :
    f ⁻¹ᵁ nonvanishingOpen L s =
      nonvanishingOpen (pullbackLine f L) (pullSection f s) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    let V : X.Opens := f ⁻¹ᵁ U
    let g : V.toScheme ⟶ Scheme.Opens.toScheme (X := Y) U := f.resLE U V le_rfl
    have hcomp : IsIso ((Scheme.Modules.pullback (V.ι ≫ f)).map s) := by
      rw [← Scheme.Hom.resLE_comp_ι f le_rfl]
      apply (pullback_comp_isIso_iff g (Scheme.Opens.ι (X := Y) U) s).mpr
      letI : IsIso ((Scheme.Modules.pullback (Scheme.Opens.ι (X := Y) U)).map s) := hU
      infer_instance
    have hV : IsIso (restrictSection V.ι (pullSection f s)) := by
      apply (pullback_pullSection_isIso_iff V.ι f s).mpr
      exact (pullback_comp_isIso_iff V.ι f s).mp hcomp
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨V, hV, hxU⟩
  · intro x hx
    obtain ⟨W, hW, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    obtain ⟨U, hxU, ⟨e⟩⟩ := exists_local_line_frame L (f x)
    let V : X.Opens := W ⊓ f ⁻¹ᵁ U
    have hxV : x ∈ V := ⟨hxW, hxU⟩
    let g : V.toScheme ⟶ U.toScheme := f.resLE U V inf_le_right
    have hV : IsIso (restrictSection V.ι (pullSection f s)) := by
      apply (NonvanishingLocusProof.isIso_pullback_open_iff V (pullSection f s)).mpr
      intro z
      exact (NonvanishingLocusProof.isIso_pullback_open_iff W (pullSection f s)).mp
        hW ⟨z.val, z.property.1⟩
    have hcomp : IsIso ((Scheme.Modules.pullback (g ≫ U.ι)).map s) := by
      rw [Scheme.Hom.resLE_comp_ι f inf_le_right]
      apply (pullback_comp_isIso_iff V.ι f s).mpr
      exact (pullback_pullSection_isIso_iff V.ι f s).mp hV
    have hiter := (pullback_comp_isIso_iff g U.ι s).mp hcomp
    let a : structureModule U.toScheme ⟶ structureModule U.toScheme :=
      pullSection U.ι s ≫ e.inv
    have ha : IsIso ((Scheme.Modules.pullback g).map a) := by
      letI := hiter
      change IsIso ((Scheme.Modules.pullback g).map
        ((unitPullbackIso U.ι).inv ≫ (Scheme.Modules.pullback U.ι).map s ≫ e.inv))
      simp only [Functor.map_comp]
      infer_instance
    let O : U.toScheme.Opens := U.toScheme.basicOpen (unitCoefficient a)
    have hxO : g ⟨x, hxV⟩ ∈ O :=
      image_mem_basicOpen_of_pullback_isIso g a ha ⟨x, hxV⟩
    letI : IsIso ((Scheme.Modules.pullback O.ι).map a) :=
      (unitEnd_pullback_isIso_iff O.ι a).mpr (appTop_unit_on_basicOpen (unitCoefficient a))
    have hraw : (Scheme.Modules.pullback U.ι).map s =
        (unitPullbackIso U.ι).hom ≫ a ≫ e.hom := by
      dsimp [a, pullSection, restrictSection]
      simp
    have hO : IsIso ((Scheme.Modules.pullback (O.ι ≫ U.ι)).map s) := by
      apply (pullback_comp_isIso_iff O.ι U.ι s).mpr
      rw [hraw]
      simp only [Functor.map_comp]
      infer_instance
    have hmem := image_mem_nonvanishing_of_open_isIso (O.ι ≫ U.ι) L s hO
      ⟨g ⟨x, hxV⟩, hxO⟩
    change U.ι (g ⟨x, hxV⟩) ∈ nonvanishingOpen L s at hmem
    have hpoint : U.ι (g ⟨x, hxV⟩) = f x := by
      exact congrArg (fun q => q ⟨x, hxV⟩)
        (Scheme.Hom.resLE_comp_ι f (show V ≤ f ⁻¹ᵁ U from inf_le_right))
    change f x ∈ nonvanishingOpen L s
    rwa [hpoint] at hmem

end LeBrunSalamon.NonvanishingPullbackProof

end

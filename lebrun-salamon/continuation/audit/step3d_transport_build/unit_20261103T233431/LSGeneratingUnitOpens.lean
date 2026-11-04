import RecompileExtensionsPart01
import LSNonvanishingPullback

/-! Unit-open cover for an actual generating tuple of an invertible sheaf.
The proof uses the original epimorphism, a local lift of 1, finite coproduct
reconstruction, and the local-ring criterion for a finite sum to be a unit.
No new admitted input is introduced. Compiler receipts record the exact
source and the scope of dependency verification. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.NonvanishingPullbackProof

namespace LeBrunSalamon.GeneratingUnitOpens

/-- Pullback and an actual local frame preserve generation by the original
finite tuple, with the free-sheaf comparison normalized on each inclusion. -/
theorem pulled_tuple_generates {Y T : Scheme.{0}} {N : ℕ} (L : LineBundle Y)
    (a : Fin (N+1) → AlgebraicSection L.sheaf) (ha : TupleGenerates L a)
    (f : T ⟶ Y) (e : pullbackModule f L.sheaf ≅ structureModule T) :
    Epi (Sigma.desc (fun i => pullSection f (a i) ≫ e.hom)) := by
  let F : SheafOfModules.{0} Y.ringCatSheaf ⥤ SheafOfModules.{0} T.ringCatSheaf :=
    Scheme.Modules.pullback f
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).isLeftAdjoint
  let q : SheafOfModules.free (R := Y.ringCatSheaf) (Fin (N+1)) ⟶ L.sheaf :=
    Sigma.desc a
  letI : Epi q := ha
  letI : Epi (F.map q) := inferInstance
  let c := SheafOfModules.mapFreeIso F (Fin (N+1)) (unitPullbackIso f).symm
  have h : Sigma.desc (fun i => pullSection f (a i) ≫ e.hom) =
      c.hom ≫ F.map q ≫ e.hom := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc]
    change pullSection f (a i) ≫ e.hom =
      SheafOfModules.ιFree i ≫ c.hom ≫ F.map q ≫ e.hom
    erw [SheafOfModules.ιFree_mapFreeIso_hom_assoc, ← Functor.map_comp_assoc]
    simp only [q, SheafOfModules.ιFree, Sigma.ι_comp_desc,
      pullSection, restrictSection, F, Iso.symm_hom, Category.assoc]
  rw [h]
  infer_instance

theorem unit_app_eq_mul {X : Scheme.{0}}
    (a : structureModule X ⟶ structureModule X) (U : X.Opens)
    (c : RingSections X U) :
    a.app U c = c * X.presheaf.map (homOfLE le_top).op (unitCoefficient a) := by
  have ha : a.app U (1 : RingSections X U) =
      X.presheaf.map (homOfLE le_top).op (unitCoefficient a) := by
    have h := sheafHom_naturality a (homOfLE (show U ≤ ⊤ from le_top))
      (1 : RingSections X ⊤)
    change X.presheaf.map (homOfLE le_top).op (unitCoefficient a) =
      a.app U (X.presheaf.map (homOfLE le_top).op (1 : RingSections X ⊤)) at h
    simpa only [map_one] using h.symm
  have h := Scheme.Modules.Hom.app_smul a c (1 : RingSections X U)
  simpa only [smul_eq_mul, mul_one, ha] using h

/-- A finite generating tuple of unit-sheaf endomorphisms has a unit germ
at each point. This uses the actual categorical epi, not a fiber surrogate. -/
theorem scalar_tuple_basicOpen_cover {X : Scheme.{0}} {N : ℕ}
    (a : Fin (N+1) → (structureModule X ⟶ structureModule X))
    [Epi (Sigma.desc a)] (x : X) :
    ∃ i, x ∈ X.basicOpen (unitCoefficient (a i)) := by
  classical
  let q := Sigma.desc a
  obtain ⟨U, hU, hxU, ⟨t⟩⟩ :=
    LocalExtensionSplitting.exists_unitLift_neighborhood q ⊤ x (by trivial)
  let E := fun _ : Fin (N+1) => structureModule X
  let c : Fin (N+1) → RingSections X U := fun i => (Sigma.π E i).app U t.val
  have hsum : (∑ i, c i * X.presheaf.map (homOfLE le_top).op
      (unitCoefficient (a i))) = (1 : RingSections X U) := by
    calc
      _ = ∑ i, (a i).app U ((Sigma.π E i).app U t.val) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (unit_app_eq_mul (a i) U (c i)).symm
      _ = ∑ i, q.app U ((Sigma.ι E i).app U ((Sigma.π E i).app U t.val)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (congrArg (fun f => f.app U ((Sigma.π E i).app U t.val))
          (Sigma.ι_comp_desc a i)).symm
      _ = q.app U (∑ i, (Sigma.ι E i).app U ((Sigma.π E i).app U t.val)) :=
        (map_sum (q.app U).hom _ _).symm
      _ = (1 : RingSections X U) := by
        rw [DirectSumCech.coproduct_section_total E U t.val]
        exact t.property
  let g := X.presheaf.germ U x hxU
  have hsumg : (∑ i, g (c i * X.presheaf.map (homOfLE le_top).op
      (unitCoefficient (a i)))) = 1 := by
    simpa only [map_sum, map_one] using congrArg g hsum
  obtain ⟨i, hi, hui⟩ := IsLocalRing.exists_of_isUnit_sum
    (s := Finset.univ) (f := fun i => g (c i * X.presheaf.map
      (homOfLE le_top).op (unitCoefficient (a i))))
      (by rw [hsumg]; exact isUnit_one)
  have hu : IsUnit (g (X.presheaf.map (homOfLE le_top).op
      (unitCoefficient (a i)))) := by
    exact isUnit_of_mul_isUnit_right (by simpa only [map_mul] using hui)
  refine ⟨i, ?_⟩
  apply (X.toRingedSpace.mem_basicOpen (unitCoefficient (a i)) x (by trivial)).mpr
  simpa only [g, X.presheaf.germ_res_apply] using hu

/-- The original generating sections cover by their actual nonvanishing
opens. The scalar unit germ is promoted to its basic-open neighborhood. -/
theorem generating_nonvanishing_cover {Y : Scheme.{0}} {N : ℕ}
    (L : LineBundle Y) (a : Fin (N+1) → AlgebraicSection L.sheaf)
    (ha : TupleGenerates L a) :
    (⨆ i, nonvanishingOpen L (a i)) = ⊤ := by
  classical
  apply top_unique
  intro y hy
  obtain ⟨U, hyU, ⟨e⟩⟩ := exists_local_line_frame L y
  let b : Fin (N+1) → (structureModule U.toScheme ⟶ structureModule U.toScheme) :=
    fun i => pullSection U.ι (a i) ≫ e.inv
  letI : Epi (Sigma.desc b) := pulled_tuple_generates L a ha U.ι e.symm
  obtain ⟨i, hi⟩ := scalar_tuple_basicOpen_cover b ⟨y, hyU⟩
  let V : U.toScheme.Opens := U.toScheme.basicOpen (unitCoefficient (b i))
  letI : IsIso ((Scheme.Modules.pullback V.ι).map (b i)) :=
    (unitEnd_pullback_isIso_iff V.ι (b i)).mpr
      (appTop_unit_on_basicOpen (unitCoefficient (b i)))
  have hraw : (Scheme.Modules.pullback U.ι).map (a i) =
      (unitPullbackIso U.ι).hom ≫ b i ≫ e.hom := by
    dsimp [b, pullSection, restrictSection]
    simp
  have hV : IsIso ((Scheme.Modules.pullback (V.ι ≫ U.ι)).map (a i)) := by
    apply (pullback_comp_isIso_iff V.ι U.ι (a i)).mpr
    rw [hraw]
    simp only [Functor.map_comp]
    infer_instance
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  exact image_mem_nonvanishing_of_open_isIso (V.ι ≫ U.ι) L (a i) hV
    ⟨⟨y, hyU⟩, hi⟩

/-- The requested unit-open universal property, now a theorem about the
specific nonvanishing opens and original section pullbacks. -/
theorem generating_sections_unitOpen {Y : Scheme.{0}} {N : ℕ}
    (L : LineBundle Y) (a : Fin (N+1) → AlgebraicSection L.sheaf)
    (ha : TupleGenerates L a) :
    ∃ U : Fin (N+1) → Y.Opens, iSup U = ⊤ ∧
      ∀ (i : Fin (N+1)) (T : Scheme) (f : T ⟶ Y),
        Set.range f ⊆ (U i : Set Y) ↔ IsIso (pullSection f (a i)) := by
  refine ⟨fun i => nonvanishingOpen L (a i), generating_nonvanishing_cover L a ha, ?_⟩
  intro i T f
  change Set.range f ⊆ (nonvanishingOpen L (a i) : Set Y) ↔ _
  have hnv := nonvanishingOpen_eq_top_iff (pullbackLine f L) (pullSection f (a i))
  change (nonvanishingOpen (pullbackLine f L) (pullSection f (a i)) = ⊤) ↔
    IsIso (pullSection f (a i)) at hnv
  rw [← hnv, ← NonvanishingPullbackProof.nonvanishingOpen_pullback]
  constructor
  · intro h
    apply top_unique
    intro x hx
    exact h ⟨x, rfl⟩
  · intro h
    rintro y ⟨x, rfl⟩
    change x ∈ f ⁻¹ᵁ nonvanishingOpen L (a i)
    rw [h]
    trivial

end LeBrunSalamon.GeneratingUnitOpens

end

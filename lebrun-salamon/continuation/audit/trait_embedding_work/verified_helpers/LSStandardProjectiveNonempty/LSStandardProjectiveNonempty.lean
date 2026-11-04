import LSStandardTautological

/-! A standard coordinate point and nonvanishing of a monomorphic
section.  These are actual construction and stalk arguments, with no
admitted nonemptiness or coefficient criterion. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.StandardProjectiveNonempty

theorem structure_id_ne_zero {Y : Scheme.{0}} (x : Y) :
    (𝟙 (structureModule Y)) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : structureModule Y ⟶ structureModule Y =>
    f.app ⊤ (1 : RingSections Y ⊤)) h
  change (1 : RingSections Y ⊤) = 0 at hh
  have hg := congrArg (Y.presheaf.germ ⊤ x (by trivial)) hh
  exact one_ne_zero (by simpa only [map_one, map_zero] using hg)

theorem section_ne_zero_of_mono {Y : Scheme.{0}} (x : Y) {E : OModule Y}
    (s : AlgebraicSection E) [Mono s] : s ≠ 0 := by
  intro hs
  apply structure_id_ne_zero x
  apply (cancel_mono s).mp
  rw [hs, comp_zero, zero_comp]

theorem nonempty (K : Type) [Field K] (N : ℕ) :
    Nonempty (StandardTautological.space K N) := by
  let X := Spec (CommRingCat.of K)
  let E := structureModule X
  let a : Fin (N+1) → AlgebraicSection E := fun i => if i = 0 then 𝟙 E else 0
  let q : SheafOfModules.free (R := X.ringCatSheaf) (Fin (N+1)) ⟶ E := Sigma.desc a
  let inc := Sigma.ι (fun _ : Fin (N+1) => E) (0 : Fin (N+1))
  have hi : inc ≫ q = 𝟙 E := by
    rw [Sigma.ι_comp_desc]
    simp only [a, ite_true]
  letI : Epi (inc ≫ q) := by rw [hi]; infer_instance
  have hq : Epi q := epi_of_epi inc q
  obtain ⟨f, _, _⟩ := (StandardTautological.chosen K N).universal
    X (𝟙 X) E (structureModule_rank X) a hq
  exact ⟨f.val (default : PrimeSpectrum K)⟩

end LeBrunSalamon.StandardProjectiveNonempty
end

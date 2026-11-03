import LSRelativeGenericSmoothness
import Mathlib.Topology.Sober
import Mathlib.Topology.NoetherianSpace

/-!
## An actual integral affine source for a dominant finite-type family

A finite-type parameter scheme may be reducible or nonreduced. The
ordinary argument below finds a point above the generic target point,
takes an actual affine chart there, and quotients by its actual prime
ideal. The resulting integral affine scheme still maps dominantly to
the target, through the original family. No component or dominance
witness is added to the original deformation data.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.Construction.Lines.FiniteTypeDominance

section Topology

open TopologicalSpace

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
variable [T0Space Y] [QuasiSober Y] [NoetherianSpace Y]
variable [T0Space Z] [QuasiSober Z] [IrreducibleSpace Z]

/-- Finitely many source generic points already have dense image.
One of them must map to the actual generic point of an irreducible target.
This is a topological deduction, with no Chevalley or smoothness input. -/
theorem exists_map_genericPoint (f : Y → Z) (hf : Continuous f)
    (hd : DenseRange f) : ∃ y : Y, f y = genericPoint Z := by
  have hfinite : (genericPoints Y).Finite :=
    genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hclosure : closure (f '' genericPoints Y) = Set.univ := by
    calc
      closure (f '' genericPoints Y) = closure (f '' closure (genericPoints Y)) :=
        (closure_image_closure hf).symm
      _ = Set.univ := by rw [genericPoints.closure, Set.image_univ, hd.closure_range]
  have himage : f '' genericPoints Y = ⋃ y ∈ genericPoints Y, ({f y} : Set Z) :=
    Set.image_eq_iUnion f (genericPoints Y)
  rw [himage, hfinite.closure_biUnion] at hclosure
  have hη : genericPoint Z ∈ ⋃ y ∈ genericPoints Y, closure ({f y} : Set Z) := by
    rw [hclosure]
    trivial
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hη
  obtain ⟨hy, hηy⟩ := Set.mem_iUnion.mp hy
  have hfy : IsGenericPoint (f y) (Set.univ : Set Z) := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    exact ((genericPoint_spec Z).mem_closed_set_iff isClosed_closure).mp hηy
  exact ⟨y, hfy.eq (genericPoint_spec Z)⟩

end Topology

/-- Containing the target generic point in the actual image implies
dominance, without any reducedness assumption on the source. -/
theorem denseRange_of_genericPoint_mem_range {Y Z : Scheme}
    [IrreducibleSpace Z] (f : Y ⟶ Z)
    (h : genericPoint Z ∈ Set.range f) : DenseRange (fun y => f y) := by
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← genericPoint_closure Z]
  exact closure_mono (Set.singleton_subset_iff.mpr h)

/-- A concrete integral affine subfamily retaining dominance. The
map to the original source is the quotient by a prime in an actual
affine open chart; it is consequently locally of finite type. -/
theorem exists_integralAffine_source {Y Z : Scheme}
    [IsNoetherian Y] [IsIntegral Z]
    (f : Y ⟶ Z) (hd : DenseRange (fun y => f y)) :
    ∃ (T : Scheme) (g : T ⟶ Y),
      IsAffine T ∧ IsIntegral T ∧ LocallyOfFiniteType g ∧
        DenseRange (fun t => (g ≫ f) t) := by
  obtain ⟨y, hy⟩ := exists_map_genericPoint (fun y => f y) f.continuous hd
  obtain ⟨R, j, hj, ⟨p, hp⟩, _⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset
      (X := Y) (x := y) (U := ⊤) (by trivial)
  letI : IsOpenImmersion j := hj
  let I : Ideal R := p.asIdeal
  letI : I.IsPrime := p.isPrime
  let T : Scheme := Spec (CommRingCat.of (R ⧸ I))
  let q : T := ⟨⊥, Ideal.isPrime_bot⟩
  let k : T ⟶ Spec R := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hkq : k q = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk I) ⊥ = I
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  haveI : IsClosedImmersion k :=
    IsClosedImmersion.spec_of_quotient_mk I
  refine ⟨T, k ≫ j, inferInstance, inferInstance, inferInstance, ?_⟩
  apply denseRange_of_genericPoint_mem_range
  refine ⟨q, ?_⟩
  simpa only [Scheme.Hom.comp_apply, hkq, hp] using hy

/-- The finite-type complex wrapper derives Noetherianity from the
actual structure map before choosing the integral affine subfamily. -/
theorem finiteType_exists_integralAffine_source {Y Z : Scheme}
    [IsIntegral Z] (sY : Y ⟶ ComplexBase)
    [LocallyOfFiniteType sY] [QuasiCompact sY]
    (f : Y ⟶ Z) (hd : DenseRange (fun y => f y)) :
    ∃ (T : Scheme) (g : T ⟶ Y),
      IsAffine T ∧ IsIntegral T ∧ LocallyOfFiniteType (g ≫ sY) ∧
        QuasiCompact (g ≫ sY) ∧ DenseRange (fun t => (g ≫ f) t) := by
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  letI : IsNoetherian Y := ⟨⟩
  obtain ⟨T, g, ha, hi, hg, hdg⟩ := exists_integralAffine_source f hd
  letI := ha
  letI := hi
  letI := hg
  haveI : LocallyOfFiniteType (g ≫ sY) := inferInstance
  refine ⟨T, g, ha, hi, inferInstance, inferInstance, hdg⟩

end LeBrunSalamon.Construction.Lines.FiniteTypeDominance

end

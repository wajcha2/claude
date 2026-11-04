import RecompileExtensionsPart04Geometry
import LSP1PointTransport
import LSNodalLineTriviality

/-! Compare a supplied two-component pushout with the actual central
fibre of the fixed standard source. The branch point changes and both
inverse maps are constructed. No normal-form theorem is assumed. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.Normalization

namespace LeBrunSalamon.NodalFibreComparison

/-- Comparison of two pushouts, keeping the prescribed branch changes
and using the target's literal universal property. -/
theorem iso_of_branch_isos {A B A' B' N Y Z : Scheme}
    (p : N ⟶ A) (q : N ⟶ B) (i : A ⟶ Y) (j : B ⟶ Y)
    (hpush : IsPushout p q i j)
    (p' : N ⟶ A') (q' : N ⟶ B') (i' : A' ⟶ Z) (j' : B' ⟶ Z)
    (hnode : p' ≫ i' = q' ≫ j')
    (huniv : ∀ (T : Scheme) (l : A' ⟶ T) (r : B' ⟶ T),
      p' ≫ l = q' ≫ r → ∃! f : Z ⟶ T, i' ≫ f = l ∧ j' ≫ f = r)
    (eA : A ≅ A') (eB : B ≅ B')
    (hp : p ≫ eA.hom = p') (hq : q ≫ eB.hom = q') :
    ∃ e : Y ≅ Z, i ≫ e.hom = eA.hom ≫ i' ∧ j ≫ e.hom = eB.hom ≫ j' := by
  have hp' : p' ≫ eA.inv = p := by rw [← hp]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hq' : q' ≫ eB.inv = q := by rw [← hq]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfnode : p ≫ (eA.hom ≫ i') = q ≫ (eB.hom ≫ j') := by
    rw [← Category.assoc, hp, ← Category.assoc, hq, hnode]
  let f := hpush.desc (eA.hom ≫ i') (eB.hom ≫ j') hfnode
  have hfi : i ≫ f = eA.hom ≫ i' := hpush.inl_desc _ _ _
  have hfj : j ≫ f = eB.hom ≫ j' := hpush.inr_desc _ _ _
  have hgnode : p' ≫ (eA.inv ≫ i) = q' ≫ (eB.inv ≫ j) := by
    rw [← Category.assoc, hp', ← Category.assoc, hq', hpush.w]
  obtain ⟨g, hg, _⟩ := huniv Y (eA.inv ≫ i) (eB.inv ≫ j) hgnode
  have hfg : f ≫ g = 𝟙 Y := by
    apply hpush.hom_ext
    · rw [← Category.assoc, hfi, Category.assoc, hg.1,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, hfj, Category.assoc, hg.2,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  have hgf : g ≫ f = 𝟙 Z := by
    obtain ⟨u, hu, huniq⟩ := huniv Z i' j' hnode
    apply (huniq (g ≫ f) ?_).trans (huniq (𝟙 Z) ?_).symm
    · constructor
      · rw [← Category.assoc, hg.1, Category.assoc, hfi,
          ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      · rw [← Category.assoc, hg.2, Category.assoc, hfj,
          ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · exact ⟨Category.comp_id _, Category.comp_id _⟩
  exact ⟨⟨f, g, hfg, hgf⟩, hfi, hfj⟩

/-- Arbitrary node markings are transported to the standard marking by
actual projective-line automorphisms. The resulting isomorphism is over C. -/
theorem standard_fibre_iso (F : StandardSource) (m : SourceMarks F)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (p q : ProjectiveLinePoint Lines.P) (i j : ProjectiveLine ⟶ Y)
    (hpush : IsPushout p.map q.map i j)
    (hi : i ≫ sY = Lines.P.structureMap) (hj : j ≫ sY = Lines.P.structureMap) :
    ∃ e : Y ≅ CentralFiber F, e.hom ≫ centralBase F = sY ∧
      ∃ a b : ProjectiveLine ≅ ProjectiveLine,
        p.map ≫ a.hom = Lines.marking.map ∧ q.map ≫ b.hom = Lines.marking.map ∧
        i ≫ e.hom = a.hom ≫ leftBranch m ∧
        j ≫ e.hom = b.hom ≫ rightBranch m ∧
        Nonempty (pullbackModule a.hom (projectiveCoordinates 1).hyperplane.sheaf ≅
          (projectiveCoordinates 1).hyperplane.sheaf) ∧
        Nonempty (pullbackModule b.hom (projectiveCoordinates 1).hyperplane.sheaf ≅
          (projectiveCoordinates 1).hyperplane.sheaf) := by
  obtain ⟨a, ha, hpa, hLa⟩ := P1PointTransport.exists_iso p Lines.marking
  obtain ⟨b, hb, hqb, hLb⟩ := P1PointTransport.exists_iso q Lines.marking
  obtain ⟨e, hei, hej⟩ := iso_of_branch_isos p.map q.map i j hpush
    Lines.marking.map Lines.marking.map (leftBranch m) (rightBranch m)
    (branches_meet m) (centralFiber_pushout m) a b hpa hqb
  have he : e.hom ≫ centralBase F = sY := by
    apply hpush.hom_ext
    · rw [← Category.assoc, hei, Category.assoc, leftBranch_over, hi]
      exact ha
    · rw [← Category.assoc, hej, Category.assoc, rightBranch_over, hj]
      exact hb
  exact ⟨e, he, a, b, hpa, hqb, hei, hej, hLa, hLb⟩

/-- The marked degree classifier supplies the exact sheaf comparison
when two line degrees agree. -/
theorem line_iso_of_degree_eq (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (L M : LineBundle ProjectiveLine)
    (h : projectiveLineDegree P p L = projectiveLineDegree P p M) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  obtain ⟨eL⟩ := projectiveLineDegree_spec P p L
  obtain ⟨eM⟩ := projectiveLineDegree_spec P p M
  rw [h] at eL
  exact ⟨eL ≪≫ eM.symm⟩

abbrev centralLeft (F : StandardSource) : CentralFiber F ⟶ ProjectiveLine :=
  pullback.fst F.parameter (scalarPoint 0) ≫ F.left

abbrev centralRight (F : StandardSource) : CentralFiber F ⟶ ProjectiveLine :=
  pullback.fst F.parameter (scalarPoint 0) ≫ F.right

def centralLine (F : StandardSource) : LineBundle (CentralFiber F) :=
  tensorLine (pullbackLine (centralLeft F) (projectiveCoordinates 1).hyperplane)
    (pullbackLine (centralRight F) (projectiveCoordinates 1).hyperplane)

theorem constant_line_trivial {T Y : Scheme} (s : T ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (L : LineBundle Y) :
    Nonempty (pullbackModule (s ≫ x) L.sheaf ≅ structureModule T) := by
  obtain ⟨e⟩ := ProjectiveCoordinateProof.line_at_complex_point_trivial L x
  exact ⟨((Scheme.Modules.pullbackComp s x).app L.sheaf).symm ≪≫
    (Scheme.Modules.pullback s).mapIso e ≪≫ unitPullbackIso s⟩

/-- Pulling the standard line to the reparametrized left component gives
the same actual hyperplane sheaf. The constant second factor is trivialized
through its actual value at the node. -/
theorem centralLine_left (F : StandardSource) (m : SourceMarks F)
    (a : ProjectiveLine ≅ ProjectiveLine)
    (ha : a.hom ≫ Lines.P.structureMap = Lines.P.structureMap)
    (ea : pullbackModule a.hom (projectiveCoordinates 1).hyperplane.sheaf ≅
      (projectiveCoordinates 1).hyperplane.sheaf) :
    Nonempty (pullbackModule (a.hom ≫ leftBranch m) (centralLine F).sheaf ≅
      (projectiveCoordinates 1).hyperplane.sheaf) := by
  let H := (projectiveCoordinates 1).hyperplane
  let f := a.hom ≫ leftBranch m
  have hL : f ≫ centralLeft F = a.hom := by
    simp only [f, centralLeft, leftBranch, Category.assoc, pullback.lift_fst_assoc,
      m.left_left, Category.comp_id]
  have hR : f ≫ centralRight F = Lines.P.structureMap ≫ Lines.marking.map := by
    simp only [f, centralRight, leftBranch, Category.assoc, pullback.lift_fst_assoc,
      m.left_right]
    rw [← Category.assoc, ha]
  let cL := compositionPullback f (centralLeft F) a.hom hL H.sheaf
  let cR := compositionPullback f (centralRight F)
    (Lines.P.structureMap ≫ Lines.marking.map) hR H.sheaf
  obtain ⟨eT⟩ := tensorSheaf_pullback f
    (pullbackModule (centralLeft F) H.sheaf) (pullbackModule (centralRight F) H.sheaf)
  obtain ⟨eC⟩ := constant_line_trivial Lines.P.structureMap Lines.marking.map H
  exact ⟨eT ≪≫ tensorIso (cL ≪≫ ea) (cR ≪≫ eC) ≪≫
    TensorConstruction.rightUnitIso H.sheaf⟩

theorem centralLine_right (F : StandardSource) (m : SourceMarks F)
    (b : ProjectiveLine ≅ ProjectiveLine)
    (hb : b.hom ≫ Lines.P.structureMap = Lines.P.structureMap)
    (eb : pullbackModule b.hom (projectiveCoordinates 1).hyperplane.sheaf ≅
      (projectiveCoordinates 1).hyperplane.sheaf) :
    Nonempty (pullbackModule (b.hom ≫ rightBranch m) (centralLine F).sheaf ≅
      (projectiveCoordinates 1).hyperplane.sheaf) := by
  let H := (projectiveCoordinates 1).hyperplane
  let f := b.hom ≫ rightBranch m
  have hL : f ≫ centralLeft F = Lines.P.structureMap ≫ Lines.marking.map := by
    simp only [f, centralLeft, rightBranch, Category.assoc, pullback.lift_fst_assoc,
      m.right_left]
    rw [← Category.assoc, hb]
  have hR : f ≫ centralRight F = b.hom := by
    simp only [f, centralRight, rightBranch, Category.assoc, pullback.lift_fst_assoc,
      m.right_right, Category.comp_id]
  let cL := compositionPullback f (centralLeft F)
    (Lines.P.structureMap ≫ Lines.marking.map) hL H.sheaf
  let cR := compositionPullback f (centralRight F) b.hom hR H.sheaf
  obtain ⟨eT⟩ := tensorSheaf_pullback f
    (pullbackModule (centralLeft F) H.sheaf) (pullbackModule (centralRight F) H.sheaf)
  obtain ⟨eC⟩ := constant_line_trivial Lines.P.structureMap Lines.marking.map H
  exact ⟨eT ≪≫ tensorIso (cL ≪≫ eC) (cR ≪≫ eb) ≪≫
    TensorConstruction.leftUnitIso H.sheaf⟩

/-- Comparison of the chosen degree-(1,1) line with O(1,1) on the
standard central fibre. The hyperplane degree is an explicit hypothesis
until the standard coordinate normalization is integrated. -/
theorem polarized_standard_fibre_iso (F : StandardSource) (m : SourceMarks F)
    (hH : projectiveLineDegree Lines.P Lines.marking
      (projectiveCoordinates 1).hyperplane = 1)
    {Y : Scheme.{0}} (sY : Y ⟶ ComplexBase)
    (p q : ProjectiveLinePoint Lines.P) (i j : ProjectiveLine ⟶ Y)
    (hpush : IsPushout p.map q.map i j)
    (hi : i ≫ sY = Lines.P.structureMap) (hj : j ≫ sY = Lines.P.structureMap)
    (L : LineBundle Y)
    (hLi : projectiveLineDegree Lines.P Lines.marking (pullbackLine i L) = 1)
    (hLj : projectiveLineDegree Lines.P Lines.marking (pullbackLine j L) = 1) :
    ∃ e : Y ≅ CentralFiber F, e.hom ≫ centralBase F = sY ∧
      Nonempty (L.sheaf ≅ pullbackModule e.hom (centralLine F).sheaf) := by
  obtain ⟨a, ha, hpa, ⟨hLa⟩⟩ := P1PointTransport.exists_iso p Lines.marking
  obtain ⟨b, hb, hqb, ⟨hLb⟩⟩ := P1PointTransport.exists_iso q Lines.marking
  obtain ⟨e, hei, hej⟩ := iso_of_branch_isos p.map q.map i j hpush
    Lines.marking.map Lines.marking.map (leftBranch m) (rightBranch m)
    (branches_meet m) (centralFiber_pushout m) a b hpa hqb
  have he : e.hom ≫ centralBase F = sY := by
    apply hpush.hom_ext
    · rw [← Category.assoc, hei, Category.assoc, leftBranch_over, hi]
      exact ha
    · rw [← Category.assoc, hej, Category.assoc, rightBranch_over, hj]
      exact hb
  obtain ⟨cA⟩ := centralLine_left F m a ha hLa
  obtain ⟨cB⟩ := centralLine_right F m b hb hLb
  obtain ⟨eA⟩ := line_iso_of_degree_eq Lines.P Lines.marking
    (pullbackLine i L) (projectiveCoordinates 1).hyperplane (hLi.trans hH.symm)
  obtain ⟨eB⟩ := line_iso_of_degree_eq Lines.P Lines.marking
    (pullbackLine j L) (projectiveCoordinates 1).hyperplane (hLj.trans hH.symm)
  let M := pullbackLine e.hom (centralLine F)
  let dA : pullbackModule i M.sheaf ≅ (projectiveCoordinates 1).hyperplane.sheaf :=
    compositionPullback i e.hom (a.hom ≫ leftBranch m) hei (centralLine F).sheaf ≪≫ cA
  let dB : pullbackModule j M.sheaf ≅ (projectiveCoordinates 1).hyperplane.sheaf :=
    compositionPullback j e.hom (b.hom ≫ rightBranch m) hej (centralLine F).sheaf ≪≫ cB
  exact ⟨e, he, NodalLineTriviality.line_iso_of_branch_iso
    p.map q.map i j hpush Lines.P.structureMap p.overC L M
    (eA ≪≫ dA.symm) (eB ≪≫ dB.symm)⟩

end LeBrunSalamon.NodalFibreComparison

end

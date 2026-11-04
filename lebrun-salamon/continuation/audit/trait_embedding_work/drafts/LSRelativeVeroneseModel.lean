import LSVeroneseZeroModel
import LSStandardProjectivePicard

/-! The explicit Veronese conic over R is the actual constant projective
line over Spec R, preserving the actual tensor-square line and base map.
All product and pullback comparisons are proved; the only Veronese input
is imported from the exact generic construction. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.RelativeVeroneseModel

variable {R : Type} [CommRing R] (φ : ℂ →+* R)

abbrev space : Scheme :=
  ProjectiveFibreLineRigidity.product 1 (StandardProjectiveBaseChange.base φ)

def projection : space φ ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (ProjectiveQuotient.toSpec ℂ 1) (StandardProjectiveBaseChange.base φ)

def line : LineBundle (space φ) :=
  pullbackLine (pullback.fst (ProjectiveQuotient.toSpec ℂ 1)
    (StandardProjectiveBaseChange.base φ)) (QuadraticVeronese.squareLine ℂ)

def productLineIso :
    pullbackModule (StandardProjectivePicard.productIso φ 1).hom (line φ).sheaf ≅
      (QuadraticVeronese.squareLine R).sheaf :=
  P1FamilyDegree.pullComp (StandardProjectivePicard.productIso φ 1).hom
    (pullback.fst (ProjectiveQuotient.toSpec ℂ 1) (StandardProjectiveBaseChange.base φ))
    (StandardProjectiveBaseChange.map φ 1) (StandardProjectivePicard.productIso_fst φ 1)
    (QuadraticVeronese.squareLine ℂ).sheaf ≪≫
      StandardProjectiveBaseChange.squareLineIso φ 1

theorem polarized_iso :
    ∃ e : space φ ≅ PlaneQuadratic.ZeroScheme R (QuadraticVeronese.equation R),
      e.hom ≫ PlaneQuadratic.projection R (QuadraticVeronese.equation R) = projection φ ∧
      Nonempty ((line φ).sheaf ≅ pullbackModule e.hom
        (pullbackLine (PlaneQuadratic.inclusion R (QuadraticVeronese.equation R))
          (StandardTautological.line R 2)).sheaf) := by
  obtain ⟨v, hv, dv, _⟩ := PublishedInputs.ProjectiveSpace.quadraticVeronese_zeroModel R
  let p := StandardProjectivePicard.productIso φ 1
  let e : space φ ≅ PlaneQuadratic.ZeroScheme R (QuadraticVeronese.equation R) := p.symm ≪≫ v
  have hp : p.inv ≫ StandardTautological.toSpec R 1 = projection φ := by
    rw [← StandardProjectivePicard.productIso_snd φ 1, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
    rfl
  have he : e.hom ≫ PlaneQuadratic.projection R (QuadraticVeronese.equation R) = projection φ := by
    change (p.inv ≫ v.hom) ≫ _ = _
    rw [Category.assoc, hv, hp]
  let c : pullbackModule p.inv (pullbackModule p.hom (line φ).sheaf) ≅ (line φ).sheaf :=
    P1FamilyDegree.pullComp p.inv p.hom (𝟙 _) p.inv_hom_id (line φ).sheaf ≪≫
      (Scheme.Modules.pullbackId _).app (line φ).sheaf
  let l : (line φ).sheaf ≅ pullbackModule p.inv (QuadraticVeronese.squareLine R).sheaf :=
    c.symm ≪≫ (Scheme.Modules.pullback p.inv).mapIso (productLineIso φ)
  let d : pullbackModule e.hom
      (pullbackModule (PlaneQuadratic.inclusion R (QuadraticVeronese.equation R))
        (StandardTautological.line R 2).sheaf) ≅
      pullbackModule p.inv (QuadraticVeronese.squareLine R).sheaf :=
    ((Scheme.Modules.pullbackComp p.inv v.hom).app
      (pullbackModule (PlaneQuadratic.inclusion R (QuadraticVeronese.equation R))
        (StandardTautological.line R 2).sheaf)).symm ≪≫
      (Scheme.Modules.pullback p.inv).mapIso
        (((Scheme.Modules.pullbackComp v.hom
          (PlaneQuadratic.inclusion R (QuadraticVeronese.equation R))).app
          (StandardTautological.line R 2).sheaf) ≪≫ dv)
  exact ⟨e, he, ⟨l ≪≫ d.symm⟩⟩

end LeBrunSalamon.RelativeVeroneseModel
end

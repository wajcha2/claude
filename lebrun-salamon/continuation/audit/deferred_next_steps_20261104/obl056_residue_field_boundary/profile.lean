import LSRelativeHomLiftingCorrespondenceProbe

/-! Canonical residue-field identifications for a rational section, and the
actual relative residue map in OBL056. All proofs use ordinary Mathlib APIs. -/

noncomputable section
set_option autoImplicit false
set_option profiler true
set_option stderrAsMessages false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Smoothing

namespace LeBrunSalamon.Next3i.RationalResidue

universe u

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_field_hom_isIso_of_rightInverse"

/-- A split-surjective field homomorphism is an isomorphism. -/
theorem field_hom_isIso_of_rightInverse {R S : Type u}
    [Field R] [Field S] (f : CommRingCat.of R ⟶ CommRingCat.of S)
    (g : CommRingCat.of S ⟶ CommRingCat.of R)
    (h : g ≫ f = 𝟙 (CommRingCat.of S)) : IsIso f := by
  have hsur : Function.Surjective f := by
    intro y
    refine ⟨g y, ?_⟩
    exact congrArg (fun k : CommRingCat.of S ⟶ CommRingCat.of S => k y) h
  exact (RingEquiv.ofBijective f.hom ⟨f.hom.injective, hsur⟩).toCommRingCatIso.isIso_hom

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_field_hom_isIso_of_rightInverse"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_section_point"

/-- The point equality supplied by the actual section equation. -/
theorem section_point {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of K))
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ s = 𝟙 _)
    (x : Spec (CommRingCat.of K)) : s (p x) = x := by
  change (p ≫ s) x = x
  rw [hp]
  rfl

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_section_point"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_section_residue_composite"

/-- Functoriality retains the point-transport isomorphism explicitly. -/
theorem section_residue_composite {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of K))
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ s = 𝟙 _)
    (x : Spec (CommRingCat.of K)) :
    s.residueFieldMap (p x) ≫ p.residueFieldMap x =
      ((Spec (CommRingCat.of K)).residueFieldCongr (section_point s p hp x)).hom := by
  let e := (Spec (CommRingCat.of K)).residueFieldCongr (section_point s p hp x)
  have hc : (p ≫ s).residueFieldMap x =
      e.hom ≫ Scheme.Hom.residueFieldMap (𝟙 (Spec (CommRingCat.of K))) x :=
    Scheme.Hom.residueFieldMap_congr hp x
  have hi := Scheme.residueFieldMap_id (X := Spec (CommRingCat.of K)) x
  exact (Scheme.residueFieldMap_comp p s x).symm.trans
    (hc.trans ((congrArg (fun z : (Spec (CommRingCat.of K)).residueField x ⟶
      (Spec (CommRingCat.of K)).residueField x => e.hom ≫ z) hi).trans
      (Category.comp_id e.hom)))

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_section_residue_composite"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_residueFieldMap_isIso_of_section"

/-- This is the actual residue map induced by p, not just a set-theoretic
identification of the one-point source. -/
theorem residueFieldMap_isIso_of_section {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of K))
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ s = 𝟙 _)
    (x : Spec (CommRingCat.of K)) : IsIso (p.residueFieldMap x) := by
  let e := (Spec (CommRingCat.of K)).residueFieldCongr (section_point s p hp x)
  apply field_hom_isIso_of_rightInverse (p.residueFieldMap x)
    (e.inv ≫ s.residueFieldMap (p x))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z : (Spec (CommRingCat.of K)).residueField (s (p x)) ⟶
        (Spec (CommRingCat.of K)).residueField x => e.inv ≫ z)
      (section_residue_composite s p hp x)).trans e.inv_hom_id)

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_residueFieldMap_isIso_of_section"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_residueIsoOfSection"

/-- The canonical identification with K uses the actual map induced by p. -/
def residueIsoOfSection {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of K))
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ s = 𝟙 _)
    (x : Spec (CommRingCat.of K)) : X.residueField (p x) ≅ CommRingCat.of K := by
  letI := residueFieldMap_isIso_of_section s p hp x
  exact asIso (p.residueFieldMap x) ≪≫ Scheme.Spec.residueFieldIsoOfField x

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_residueIsoOfSection"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_residueIsoOfSection_hom"

theorem residueIsoOfSection_hom {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of K))
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ s = 𝟙 _)
    (x : Spec (CommRingCat.of K)) :
    (residueIsoOfSection s p hp x).hom =
      p.residueFieldMap x ≫ (Scheme.Spec.residueFieldIsoOfField x).hom := rfl

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_residueIsoOfSection_hom"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_relative_residueFieldMap_isIso"

/-- The relative residue map is an isomorphism when the composite point
is a section over K. No smoothness, separation, or closedness is assumed. -/
theorem relative_residueFieldMap_isIso {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (s : Y ⟶ Spec (CommRingCat.of K))
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f ≫ s = 𝟙 _)
    (x : Spec (CommRingCat.of K)) : IsIso (f.residueFieldMap (p x)) := by
  letI := residueFieldMap_isIso_of_section (f ≫ s) p hp x
  have hps : (p ≫ f) ≫ s = 𝟙 _ := by simpa only [Category.assoc] using hp
  letI := residueFieldMap_isIso_of_section s (p ≫ f) hps x
  exact IsIso.of_isIso_fac_right
    (hh := residueFieldMap_isIso_of_section s (p ≫ f) hps x)
    (Scheme.residueFieldMap_comp p f x).symm

section Presentation

variable {S Y : Scheme} (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomDeformationInput.Presentation pi sS X)
    (p : ComplexBase ⟶ H.parameter)
    (hp : p ≫ H.toBase ≫ sS = 𝟙 ComplexBase)

include hp

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_relative_residueFieldMap_isIso"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_pointResidueIso"

/-- Exact residue field of the original parameter point. -/
def pointResidueIso :
    H.parameter.residueField (p (IsLocalRing.closedPoint ℂ)) ≅ CommRingCat.of ℂ :=
  residueIsoOfSection (H.toBase ≫ sS) p hp (IsLocalRing.closedPoint ℂ)

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_pointResidueIso"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_toBase_residueFieldMap_isIso"

/-- Exact relative residue map needed by the pointwise infinitesimal criterion. -/
theorem toBase_residueFieldMap_isIso :
    IsIso (H.toBase.residueFieldMap (p (IsLocalRing.closedPoint ℂ))) :=
  relative_residueFieldMap_isIso H.toBase sS p hp (IsLocalRing.closedPoint ℂ)

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_toBase_residueFieldMap_isIso"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_basePoint_overC"

/-- The supplied base point is itself a section, using the original hb. -/
theorem basePoint_overC (b : ComplexBase ⟶ S) (hb : p ≫ H.toBase = b) :
    b ≫ sS = 𝟙 ComplexBase := by
  calc
    b ≫ sS = (p ≫ H.toBase) ≫ sS := by rw [hb]
    _ = 𝟙 ComplexBase := (Category.assoc _ _ _).trans hp

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_basePoint_overC"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_basePointResidueIso"

/-- Exact residue field of the supplied base point. -/
def basePointResidueIso (b : ComplexBase ⟶ S) (hb : p ≫ H.toBase = b) :
    S.residueField (b (IsLocalRing.closedPoint ℂ)) ≅ CommRingCat.of ℂ :=
  residueIsoOfSection sS b (basePoint_overC pi sS X H p hp b hb)
    (IsLocalRing.closedPoint ℂ)

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_basePointResidueIso"

#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE ENTER_toBase_residue_compatibility"

/-- Compatibility is through the actual relative residue map and the exact
point equality from hb; no residue-field equality is inferred from singletonness. -/
theorem toBase_residue_compatibility (b : ComplexBase ⟶ S) (hb : p ≫ H.toBase = b) :
    (S.residueFieldCongr (show H.toBase (p (IsLocalRing.closedPoint ℂ)) =
        b (IsLocalRing.closedPoint ℂ) from
      congrArg (fun f : ComplexBase ⟶ S => f (IsLocalRing.closedPoint ℂ)) hb)).hom ≫
        (basePointResidueIso pi sS X H p hp b hb).hom =
      H.toBase.residueFieldMap (p (IsLocalRing.closedPoint ℂ)) ≫
        (pointResidueIso pi sS X H p hp).hom := by
  let c := IsLocalRing.closedPoint ℂ
  let e := S.residueFieldCongr (show H.toBase (p c) = b c from
    congrArg (fun f : ComplexBase ⟶ S => f c) hb)
  have hcomp : H.toBase.residueFieldMap (p c) ≫ p.residueFieldMap c =
      e.hom ≫ b.residueFieldMap c :=
    (Scheme.residueFieldMap_comp p H.toBase c).symm.trans
      (Scheme.Hom.residueFieldMap_congr hb c)
  change e.hom ≫ (b.residueFieldMap c ≫ (Scheme.Spec.residueFieldIsoOfField c).hom) =
    H.toBase.residueFieldMap (p c) ≫
      (p.residueFieldMap c ≫ (Scheme.Spec.residueFieldIsoOfField c).hom)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z : S.residueField (H.toBase (p c)) ⟶ ComplexBase.residueField c =>
      z ≫ (Scheme.Spec.residueFieldIsoOfField c).hom) hcomp.symm).trans
      (Category.assoc _ _ _))
#eval show IO Unit from do (← IO.getStderr).putStrLn "RATIONAL_RESIDUE_STAGE EXIT_toBase_residue_compatibility"


end Presentation
end LeBrunSalamon.Next3i.RationalResidue

end

#print axioms LeBrunSalamon.Next3i.RationalResidue.field_hom_isIso_of_rightInverse
#print axioms LeBrunSalamon.Next3i.RationalResidue.section_point
#print axioms LeBrunSalamon.Next3i.RationalResidue.section_residue_composite
#print axioms LeBrunSalamon.Next3i.RationalResidue.residueFieldMap_isIso_of_section
#print axioms LeBrunSalamon.Next3i.RationalResidue.residueIsoOfSection
#print axioms LeBrunSalamon.Next3i.RationalResidue.residueIsoOfSection_hom
#print axioms LeBrunSalamon.Next3i.RationalResidue.relative_residueFieldMap_isIso
#print axioms LeBrunSalamon.Next3i.RationalResidue.pointResidueIso
#print axioms LeBrunSalamon.Next3i.RationalResidue.toBase_residueFieldMap_isIso
#print axioms LeBrunSalamon.Next3i.RationalResidue.basePoint_overC
#print axioms LeBrunSalamon.Next3i.RationalResidue.basePointResidueIso
#print axioms LeBrunSalamon.Next3i.RationalResidue.toBase_residue_compatibility

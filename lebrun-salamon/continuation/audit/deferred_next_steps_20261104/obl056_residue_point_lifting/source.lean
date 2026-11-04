import Mathlib

/-! Lifting an actual field-valued point along a residue-field isomorphism.
No Artinian, smoothness, flatness, or project presentation assumption is used.
The canonical residue-point factorization supplies the actual map and centre. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace LeBrunSalamon.Next3i.ResiduePointLifting

universe u

variable {T X : Scheme.{u}} (f : T ⟶ X) (t : T)
    [hres : IsIso (f.residueFieldMap t)]
    (K : Type u) [Field K] (p : Spec (CommRingCat.of K) ⟶ X)
    (hp : p (IsLocalRing.closedPoint K) = f t)

/-- The actual residue-field embedding defining the lifted point retains
the point-equality transport and the inverse of the given residue map. -/
def residuePointLift : Spec (CommRingCat.of K) ⟶ T :=
  Spec.map (inv (f.residueFieldMap t) ≫
      (X.residueFieldCongr hp.symm).hom ≫
      X.descResidueField (Scheme.stalkClosedPointTo p)) ≫
    T.fromSpecResidueField t

/-- The constructed map lifts the supplied field-valued point itself. -/
theorem residuePointLift_comp : residuePointLift f t K p hp ≫ f = p := by
  let e := X.residueFieldCongr hp.symm
  let k := X.descResidueField (Scheme.stalkClosedPointTo p)
  let a := inv (f.residueFieldMap t) ≫ e.hom ≫ k
  change (Spec.map a ≫ T.fromSpecResidueField t) ≫ f = p
  calc
    (Spec.map a ≫ T.fromSpecResidueField t) ≫ f =
        Spec.map a ≫ (Spec.map (f.residueFieldMap t) ≫
          X.fromSpecResidueField (f t)) := by
      rw [Category.assoc, f.SpecMap_residueFieldMap_fromSpecResidueField]
    _ = Spec.map (f.residueFieldMap t ≫ a) ≫
          X.fromSpecResidueField (f t) := by
      simp only [Spec.map_comp, Category.assoc]
    _ = Spec.map (e.hom ≫ k) ≫ X.fromSpecResidueField (f t) := by
      dsimp only [a]
      rw [IsIso.hom_inv_id_assoc]
    _ = Spec.map k ≫ X.fromSpecResidueField (p (IsLocalRing.closedPoint K)) := by
      rw [Spec.map_comp, Category.assoc]
      exact congrArg (fun z : Spec (X.residueField (p (IsLocalRing.closedPoint K))) ⟶ X =>
        Spec.map k ≫ z) (X.residueFieldCongr_fromSpecResidueField hp.symm)
    _ = p := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X p

/-- Its closed point is the specified source point, not just some point over it. -/
theorem residuePointLift_closedPoint :
    residuePointLift f t K p hp (IsLocalRing.closedPoint K) = t := by
  change T.fromSpecResidueField t
    (Spec.map (inv (f.residueFieldMap t) ≫
      (X.residueFieldCongr hp.symm).hom ≫
      X.descResidueField (Scheme.stalkClosedPointTo p))
        (IsLocalRing.closedPoint K)) = t
  exact T.fromSpecResidueField_apply t _

include hp hres in
theorem exists_residuePointLift :
    ∃ q : Spec (CommRingCat.of K) ⟶ T,
      q ≫ f = p ∧ q (IsLocalRing.closedPoint K) = t :=
  ⟨residuePointLift f t K p hp, residuePointLift_comp f t K p hp,
    residuePointLift_closedPoint f t K p hp⟩

/-- Any existing structural square is respected by this actual lift. -/
theorem residuePointLift_overBase {S : Scheme.{u}} (s : X ⟶ S)
    (sT : T ⟶ S) (b : Spec (CommRingCat.of K) ⟶ S)
    (hf : f ≫ s = sT) (hb : p ≫ s = b) :
    residuePointLift f t K p hp ≫ sT = b := by
  calc
    residuePointLift f t K p hp ≫ sT =
        residuePointLift f t K p hp ≫ (f ≫ s) := by rw [hf]
    _ = (residuePointLift f t K p hp ≫ f) ≫ s := (Category.assoc _ _ _).symm
    _ = p ≫ s := congrArg (fun a : Spec (CommRingCat.of K) ⟶ X => a ≫ s)
      (residuePointLift_comp f t K p hp)
    _ = b := hb

include hp hres in
theorem exists_compatible_residuePointLift {S : Scheme.{u}} (s : X ⟶ S)
    (sT : T ⟶ S) (b : Spec (CommRingCat.of K) ⟶ S)
    (hf : f ≫ s = sT) (hb : p ≫ s = b) :
    ∃ q : Spec (CommRingCat.of K) ⟶ T,
      q ≫ f = p ∧ q (IsLocalRing.closedPoint K) = t ∧ q ≫ sT = b :=
  ⟨residuePointLift f t K p hp, residuePointLift_comp f t K p hp,
    residuePointLift_closedPoint f t K p hp,
    residuePointLift_overBase f t K p hp s sT b hf hb⟩

/-- The local-ring test used by the pointwise criterion is an immediate
specialization; no extra property of the local ring is needed. -/
theorem exists_localTestCentre {B : Type u} [CommRing B] [IsLocalRing B]
    {Z S : Scheme.{u}} (alpha : Spec (CommRingCat.of B) ⟶ Z)
    [IsIso (alpha.residueFieldMap (IsLocalRing.closedPoint B))]
    (L : Type u) [Field L] (p₀ : Spec (CommRingCat.of L) ⟶ Z)
    (hcentre : p₀ (IsLocalRing.closedPoint L) = alpha (IsLocalRing.closedPoint B))
    (s : Z ⟶ S) (sB : Spec (CommRingCat.of B) ⟶ S)
    (b : Spec (CommRingCat.of L) ⟶ S)
    (halpha : alpha ≫ s = sB) (hb : p₀ ≫ s = b) :
    ∃ i : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of B),
      i ≫ alpha = p₀ ∧ i (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint B ∧
        i ≫ sB = b :=
  exists_compatible_residuePointLift alpha (IsLocalRing.closedPoint B) L p₀ hcentre
    s sB b halpha hb

end LeBrunSalamon.Next3i.ResiduePointLifting

end

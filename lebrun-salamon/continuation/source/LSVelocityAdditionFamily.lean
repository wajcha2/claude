import LSScaledVelocities

/-!
## The actual nonorthogonal Hom-velocity addition family

The source is a product of the actual bounded scalar line families,
restricted by the actual Levi polynomial. Its complex points cover the
nonorthogonal component-cone pairs, so the proved cone-addition dominance
transfers to this source. All maps and their coordinate functions are
fixed before generic smoothness is used.

Source preparation only; no compiler has been invoked.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open scoped TensorProduct

namespace LeBrunSalamon.Construction.Lines.VelocityAdditionFamily

open DirectionCones ConeGeometry SectionAlgebra VelocityCoordinates GlobalCoordinates

section ConePoints
variable {I : Type} [Fintype I]

/-- Every actual complex point of the nonorthogonal cone product is an
actual nonorthogonal pair of its equation-closed coordinate sets. -/
theorem conePoint_coordinates (S T : Set (I → ℂ))
    (hS : EquationClosed S) (hT : EquationClosed T) (omega : I → I → ℂ)
    (p : PointsOver ComplexBase (𝟙 ComplexBase) (nonorthogonalOpen S T omega).toScheme
      ((nonorthogonalOpen S T omega).ι ≫ affineBaseMap (ProductRing S T))) :
    ∃ (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T),
      ConePairing.pairing omega a b ≠ 0 ∧
        p.val ≫ nonorthogonalAddition S T omega = coordinatePoint (a + b) := by
  let q : ProductRing S T →ₐ[ℂ] ℂ := GlobalVelocity.specPoint
    (p.val ≫ (nonorthogonalOpen S T omega).ι) (by simpa only [Category.assoc] using p.property)
  let q₁ : CoordinateRing S →ₐ[ℂ] ℂ := q.comp Algebra.TensorProduct.includeLeft
  let q₂ : CoordinateRing T →ₐ[ℂ] ℂ := q.comp Algebra.TensorProduct.includeRight
  let a : I → ℂ := fun i => q₁ (coordinate S i)
  let b : I → ℂ := fun i => q₂ (coordinate T i)
  have ha : a ∈ S := quotientPoint_mem S hS q₁
  have hb : b ∈ T := quotientPoint_mem T hT q₂
  have hq : q = productEvaluation S T a b ha hb := by
    apply Algebra.TensorProduct.ext
    · apply quotientPoint_ext S
      intro i
      exact (productEvaluation_first S T a b ha hb i).symm
    · apply quotientPoint_ext T
      intro i
      exact (productEvaluation_second S T a b ha hb i).symm
  have hpoint : affineMap q = p.val ≫ (nonorthogonalOpen S T omega).ι :=
    GlobalVelocity.affineMap_specPoint _ _
  have hmem : affineMap q (IsLocalRing.closedPoint ℂ) ∈ nonorthogonalOpen S T omega := by
    rw [hpoint]
    exact (p.val (IsLocalRing.closedPoint ℂ)).property
  have hab : ConePairing.pairing omega a b ≠ 0 := by
    rw [hq] at hmem
    exact (pairPoint_mem_nonorthogonalOpen S T omega a b ha hb (IsLocalRing.closedPoint ℂ)).mp hmem
  refine ⟨a, b, ha, hb, hab, ?_⟩
  rw [nonorthogonalAddition, ← Category.assoc, ← hpoint, hq]
  exact pairPoint_addition S T a b ha hb

end ConePoints

variable {n : ℕ} (X : ContactFanoManifold n)
variable (H : HomSpacePresentation P X.variety)
variable (D : HomDegree.Open P marking X.variety H X.contact.sequence.line 1)
variable (x : ComplexPoint X.variety) (C : GlobalVelocity.TargetChart X.variety x)

abbrev Index := ScaledVelocities.Index (n := n)
abbrev pairParameter : Scheme :=
  pullback (ScaledVelocities.toC X H D x) (ScaledVelocities.toC X H D x)

def first : pairParameter X H D x ⟶ ScaledVelocities.parameter X H D x := pullback.fst _ _
def second : pairParameter X H D x ⟶ ScaledVelocities.parameter X H D x := pullback.snd _ _
def pairToC : pairParameter X H D x ⟶ ComplexBase := first X H D x ≫ ScaledVelocities.toC X H D x

@[reassoc] theorem second_overC : second X H D x ≫ ScaledVelocities.toC X H D x = pairToC X H D x :=
  pullback.condition.symm

instance pairToC_finiteType : LocallyOfFiniteType (pairToC X H D x) := by
  dsimp [pairToC, first]
  infer_instance

instance pairToC_quasiCompact : QuasiCompact (pairToC X H D x) := by
  dsimp [pairToC, first]
  infer_instance

instance pairParameter_noetherian : IsNoetherian (pairParameter X H D x) := by
  letI : IsLocallyNoetherian (pairParameter X H D x) :=
    LocallyOfFiniteType.isLocallyNoetherian (pairToC X H D x)
  letI : CompactSpace (pairParameter X H D x) :=
    QuasiCompact.compactSpace_of_compactSpace (pairToC X H D x)
  exact ⟨⟩

def firstCoordinates (i : Index (n := n)) : Functions (pairToC X H D x) ⊤ :=
  onFunctionsTop (first X H D x) rfl (ScaledVelocities.coordinates X H D x C i)

def secondCoordinates (i : Index (n := n)) : Functions (pairToC X H D x) ⊤ :=
  onFunctionsTop (second X H D x) (second_overC X H D x) (ScaledVelocities.coordinates X H D x C i)

def sumCoordinates (i : Index (n := n)) : Functions (pairToC X H D x) ⊤ :=
  firstCoordinates X H D x C i + secondCoordinates X H D x C i

def pairingFunction : Functions (pairToC X H D x) ⊤ :=
  ConePairing.pairing (omega X x C) (firstCoordinates X H D x C) (secondCoordinates X H D x C)

def nonorthogonalOpen : (pairParameter X H D x).Opens :=
  (pairParameter X H D x).basicOpen (pairingFunction X H D x C)

abbrev parameter : Scheme := (nonorthogonalOpen X H D x C).toScheme
def toC : parameter X H D x C ⟶ ComplexBase := (nonorthogonalOpen X H D x C).ι ≫ pairToC X H D x

def morphism : parameter X H D x C ⟶ affineSpace (Index (n := n)) :=
  (nonorthogonalOpen X H D x C).ι ≫ GlobalCoordinates.map (pairToC X H D x) (sumCoordinates X H D x C)

@[reassoc] theorem morphism_overC :
    morphism X H D x C ≫ affineBaseMap (MvPolynomial (Index (n := n)) ℂ) = toC X H D x C := by
  rw [morphism, Category.assoc, GlobalCoordinates.map_overC]
  rfl

instance toC_finiteType : LocallyOfFiniteType (toC X H D x C) := by
  dsimp [toC]
  infer_instance

instance toC_quasiCompact : QuasiCompact (toC X H D x C) := by
  letI : TopologicalSpace.NoetherianSpace (parameter X H D x C) :=
    (nonorthogonalOpen X H D x C).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

def firstScaled : parameter X H D x C ⟶ ScaledVelocities.parameter X H D x :=
  (nonorthogonalOpen X H D x C).ι ≫ first X H D x

def secondScaled : parameter X H D x C ⟶ ScaledVelocities.parameter X H D x :=
  (nonorthogonalOpen X H D x C).ι ≫ second X H D x

@[reassoc] theorem firstScaled_overC : firstScaled X H D x C ≫ ScaledVelocities.toC X H D x = toC X H D x C := by
  exact Category.assoc _ _ _

@[reassoc] theorem secondScaled_overC : secondScaled X H D x C ≫ ScaledVelocities.toC X H D x = toC X H D x C := by
  rw [secondScaled, Category.assoc, second_overC]
  rfl

def pairPoint
    (t u : PointsOver ComplexBase (𝟙 ComplexBase)
      (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x)) :
    PointsOver ComplexBase (𝟙 ComplexBase) (pairParameter X H D x) (pairToC X H D x) :=
  ⟨pullback.lift t.val u.val (t.property.trans u.property.symm), by
    simp only [pairToC, first, ← Category.assoc, pullback.lift_fst, t.property]⟩

theorem pairPoint_firstCoordinates
    (t u : PointsOver ComplexBase (𝟙 ComplexBase)
      (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x)) (i : Index (n := n)) :
    GlobalCoordinates.evaluation (pairPoint X H D x t u) (firstCoordinates X H D x C i) =
      GlobalCoordinates.evaluation t (ScaledVelocities.coordinates X H D x C i) := by
  change GlobalCoordinates.evaluation (pairPoint X H D x t u)
    (onFunctionsTop (sY := pairToC X H D x) (first X H D x) rfl
      (ScaledVelocities.coordinates X H D x C i)) = _
  rw [GlobalCoordinates.evaluation_precompose]
  apply congrArg (fun z : PointsOver ComplexBase (𝟙 ComplexBase)
    (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x) =>
      GlobalCoordinates.evaluation z (ScaledVelocities.coordinates X H D x C i))
  apply Subtype.ext
  exact pullback.lift_fst _ _ _

theorem pairPoint_secondCoordinates
    (t u : PointsOver ComplexBase (𝟙 ComplexBase)
      (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x)) (i : Index (n := n)) :
    GlobalCoordinates.evaluation (pairPoint X H D x t u) (secondCoordinates X H D x C i) =
      GlobalCoordinates.evaluation u (ScaledVelocities.coordinates X H D x C i) := by
  change GlobalCoordinates.evaluation (pairPoint X H D x t u)
    (onFunctionsTop (second X H D x) (second_overC X H D x) (ScaledVelocities.coordinates X H D x C i)) = _
  rw [GlobalCoordinates.evaluation_precompose]
  apply congrArg (fun z : PointsOver ComplexBase (𝟙 ComplexBase)
    (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x) =>
      GlobalCoordinates.evaluation z (ScaledVelocities.coordinates X H D x C i))
  apply Subtype.ext
  exact pullback.lift_snd _ _ _

theorem pairPoint_pairing
    (t u : PointsOver ComplexBase (𝟙 ComplexBase)
      (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x)) :
    GlobalCoordinates.evaluation (pairPoint X H D x t u) (pairingFunction X H D x C) =
      ConePairing.pairing (omega X x C)
        (fun i => GlobalCoordinates.evaluation t (ScaledVelocities.coordinates X H D x C i))
        (fun i => GlobalCoordinates.evaluation u (ScaledVelocities.coordinates X H D x C i)) := by
  unfold pairingFunction
  rw [ConePairing.pairing_map]
  simp only [pairPoint_firstCoordinates, pairPoint_secondCoordinates]

theorem nonorthogonalPair_covered
    (a b : Index (n := n) → ℂ)
    (ha : IsSelectedVector (fun _ : FreeLine X => True) x ((contactFrame X x C).symm a))
    (hb : IsSelectedVector (fun _ : FreeLine X => True) x ((contactFrame X x C).symm b))
    (hab : ConePairing.pairing (omega X x C) a b ≠ 0) :
    ∃ t : PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x C) (toC X H D x C),
      t.val ≫ morphism X H D x C = coordinatePoint (a + b) := by
  obtain ⟨t, ht⟩ := ScaledVelocities.selectedVector_coordinate_covered X H D x C _ ha
  obtain ⟨u, hu⟩ := ScaledVelocities.selectedVector_coordinate_covered X H D x C _ hb
  rw [LinearEquiv.apply_symm_apply] at ht hu
  let p := pairPoint X H D x t u
  have hp : p.val (IsLocalRing.closedPoint ℂ) ∈ nonorthogonalOpen X H D x C := by
    apply (GlobalCoordinates.point_mem_basicOpen p (pairingFunction X H D x C)).mpr
    rw [pairPoint_pairing, ht, hu]
    exact hab
  let q := HomDegree.pointInOpen p (nonorthogonalOpen X H D x C) hp
  refine ⟨q, ?_⟩
  rw [morphism, ← Category.assoc, HomDegree.pointInOpen_inclusion, GlobalCoordinates.map_point]
  congr 1
  funext i
  change GlobalCoordinates.evaluation p
    (firstCoordinates X H D x C i + secondCoordinates X H D x C i) = a i + b i
  rw [map_add, pairPoint_firstCoordinates, pairPoint_secondCoordinates,
    congrFun ht i, congrFun hu i]

theorem conePair_covered
    (V : PublishedDirections.LegendrianDirections X x C) (K E : V.directions.Component)
    (p : PointsOver ComplexBase (𝟙 ComplexBase)
      (ConeGeometry.nonorthogonalOpen
        (V.directions.componentConePoints (contactFrame X x C) K)
        (V.directions.componentConePoints (contactFrame X x C) E) (omega X x C)).toScheme
      ((ConeGeometry.nonorthogonalOpen
        (V.directions.componentConePoints (contactFrame X x C) K)
        (V.directions.componentConePoints (contactFrame X x C) E) (omega X x C)).ι ≫
        affineBaseMap (ProductRing
          (V.directions.componentConePoints (contactFrame X x C) K)
          (V.directions.componentConePoints (contactFrame X x C) E)))) :
    ∃ t : PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x C) (toC X H D x C),
      t.val ≫ morphism X H D x C = p.val ≫ nonorthogonalAddition
        (V.directions.componentConePoints (contactFrame X x C) K)
        (V.directions.componentConePoints (contactFrame X x C) E) (omega X x C) := by
  obtain ⟨a, b, ha, hb, hab, hp⟩ := conePoint_coordinates _ _ (V.cone_closed K) (V.cone_closed E)
    (omega X x C) p
  have ha0 : a ≠ 0 := by
    intro h
    apply hab
    rw [h]
    exact ConePairing.pairing_zero_left (omega X x C) b
  have hb0 : b ≠ 0 := by
    intro h
    apply hab
    rw [h]
    exact ConePairing.pairing_zero_right (omega X x C) a
  have hva0 : (contactFrame X x C).symm a ≠ 0 := by
    intro h
    apply ha0
    calc
      a = (contactFrame X x C) ((contactFrame X x C).symm a) :=
        ((contactFrame X x C).apply_symm_apply a).symm
      _ = (contactFrame X x C) 0 := congrArg (contactFrame X x C) h
      _ = 0 := map_zero (contactFrame X x C)
  have hvb0 : (contactFrame X x C).symm b ≠ 0 := by
    intro h
    apply hb0
    calc
      b = (contactFrame X x C) ((contactFrame X x C).symm b) :=
        ((contactFrame X x C).apply_symm_apply b).symm
      _ = (contactFrame X x C) 0 := congrArg (contactFrame X x C) h
      _ = 0 := map_zero (contactFrame X x C)
  have hsa := componentVector_is_actual (fun _ : FreeLine X => True) x (contactFrame X x C)
    V.directions V.realizes K ((contactFrame X x C).symm a) hva0
    ((mem_componentConePoints_iff V.directions (contactFrame X x C) K a).mp ha)
  have hsb := componentVector_is_actual (fun _ : FreeLine X => True) x (contactFrame X x C)
    V.directions V.realizes E ((contactFrame X x C).symm b) hvb0
    ((mem_componentConePoints_iff V.directions (contactFrame X x C) E b).mp hb)
  obtain ⟨t, ht⟩ := nonorthogonalPair_covered X H D x C a b hsa hsb hab
  exact ⟨t, ht.trans hp.symm⟩

/-- Dominance concerns the actual Hom family, rather than an arbitrary
scheme equipped with a requested differential-surjectivity witness. -/
theorem morphism_denseRange
    (V : PublishedDirections.LegendrianDirections X x C) (K E : V.directions.Component)
    (a b : Index (n := n) → ℂ)
    (ha : a ∈ V.directions.componentConePoints (contactFrame X x C) K)
    (hb : b ∈ V.directions.componentConePoints (contactFrame X x C) E)
    (hab : ConePairing.pairing (omega X x C) a b ≠ 0) :
    DenseRange (fun t => morphism X H D x C t) := by
  let S := V.directions.componentConePoints (contactFrame X x C) K
  let T := V.directions.componentConePoints (contactFrame X x C) E
  let U := ConeGeometry.nonorthogonalOpen S T (omega X x C)
  letI : Algebra.FiniteType ℂ (ProductRing S T) :=
    ProductGeometry.tensorProduct_finiteType (CoordinateRing S) (CoordinateRing T)
  letI : LocallyOfFiniteType (affineBaseMap (ProductRing S T)) :=
    ProductGeometry.affineBaseMap_finiteType (ProductRing S T)
  letI : LocallyOfFiniteType (U.ι ≫ affineBaseMap (ProductRing S T)) :=
    locallyOfFiniteType_comp U.ι (affineBaseMap (ProductRing S T))
  apply GlobalCoordinates.denseRange_of_point_coverage
    (U.ι ≫ affineBaseMap (ProductRing S T)) (toC X H D x C)
    (nonorthogonalAddition S T (omega X x C))
    (ProductGeometry.componentAddition_denseRange X x C V K E a b ha hb hab)
    (morphism X H D x C)
  exact conePair_covered X H D x C V K E

end LeBrunSalamon.Construction.Lines.VelocityAdditionFamily

end

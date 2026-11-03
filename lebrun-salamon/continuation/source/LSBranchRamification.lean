import LSBranchAlgebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction.Lines LeBrunSalamon.Construction.Descent

namespace LeBrunSalamon.GenericBranchGeometry

open LeBrunSalamon.Construction

/-- An actual prime Cartier divisor, its actual invertible sheaf and its
regular section. The zero scheme is specified on every affine frame;
the support equation retains the project's actual nonvanishing open. -/
structure PrimeCartierDivisor (Z : Scheme) where
  ideal : Z.IdealSheafData
  integral : IsIntegral ideal.subscheme
  line : LineBundle Z
  sectionValue : AlgebraicSection line.sheaf
  nonzero : sectionValue ≠ 0
  localEquation : ∀ F : AffineLineFrame line,
    ideal.ideal ⟨F.openSet, F.isAffine⟩ = Ideal.span {F.localCoefficient sectionValue}
  support_eq : (ideal.support : Set Z) =
    (nonvanishingOpen line sectionValue : Set Z)ᶜ

abbrev CompletedStalk (T : Scheme) (x : T) :=
  AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk x)) (T.presheaf.stalk x)

/-- The completion of the entire actual curve pullback germ, before
reduction or normalization. The source parameter is normalized through
the actual stalk map; a ring isomorphism alone would be insufficient. -/
structure FormalCurveBranch {S Z : Scheme} (q : S ⟶ Z)
    (c : ProjectiveLine ⟶ Z) (p : ProjectiveLinePoint P) where
  point : (pullback q c : Scheme)
  closed : IsClosed ({point} : Set (pullback q c : Scheme))
  overPoint : pullback.snd q c point = p.map (IsLocalRing.closedPoint ℂ)
  index : ℕ
  greaterThanOne : 1 < index
  series : PowerSeries ℂ
  transverse : SheetAlgebra.TransverseBranch.IsTransverse series
  parameter : ProjectiveLine.presheaf.stalk (pullback.snd q c point)
  parameter_generates :
    IsLocalRing.maximalIdeal (ProjectiveLine.presheaf.stalk (pullback.snd q c point)) =
      Ideal.span {parameter}
  comparison : CompletedStalk (pullback q c) point ≃+*
    SheetAlgebra.TransverseBranch.PullbackRing index series
  parameter_normalized :
    comparison (algebraMap ((pullback q c : Scheme).presheaf.stalk point)
      (CompletedStalk (pullback q c) point)
      (((pullback.snd q c).stalkMap point).hom parameter)) =
        SheetAlgebra.TransverseBranch.t index series

def familyFiber {T : Scheme} (sT : T ⟶ ComplexBase)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) T sT) :
    ProjectiveLine ⟶ RationalSourceOver P T sT :=
  pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ t.val)
    (by simp only [Category.id_comp, Category.assoc, t.property, Category.comp_id])

end LeBrunSalamon.GenericBranchGeometry

namespace LeBrunSalamon.StandardInputs

open GenericBranchGeometry

/- Approved generic branch-divisor/local-model corollary.
Sources: Stacks 31.16.7 (prime divisors on locally factorial schemes),
01X0 (actual Cartier line and section), 0EYG and 0EYF (the etale-local
Kummer model along a regular divisor). At the finite-type complex closed
points, etale local changes identify completed local rings; completing
the actual fibre product gives C[[z,t]]/(z^e-a(t)). Etaleness of the
actual divisor pullback gives a(0)=0 and a'(0)!=0. The normalization of
the curve pullback and the ramification-ideal equality are NOT outputs.

The proof first removes the proper closed bad subsets of the chosen
prime branch divisor. All residue fields at complex closed points are
C; characteristic zero makes all the relevant ramification tame.
-/
theorem finite_normal_branch_divisor_formalModel {S Z : Scheme}
    [IsIntegral S] [IsIntegral Z]
    (sZ : Z ⟶ ComplexBase) [Smooth sZ] [IsProper sZ]
    (q : S ⟶ Z) [IsFinite q] [IsDominant q]
    (hnormal : NormalScheme S) (r : S)
    (hr : ringKrullDim (S.presheaf.stalk r) = 1) (hnot : ¬ EtaleAt q r) :
    ∃ (D : PrimeCartierDivisor Z) (W : Z.Opens),
      q r ∈ D.ideal.support ∧
      ((D.ideal.support : Set Z) ∩ (W : Set Z)).Nonempty ∧
      Smooth ((D.ideal.subschemeι ⁻¹ᵁ W).ι ≫ D.ideal.subschemeι ≫ sZ) ∧
      ∀ (c : ProjectiveLine ⟶ Z) (hc : c ≫ sZ = P.structureMap)
        (p : ProjectiveLinePoint P),
        c (p.map (IsLocalRing.closedPoint ℂ)) ∈ D.ideal.support →
        c (p.map (IsLocalRing.closedPoint ℂ)) ∈ W →
        Etale (pullback.fst c D.ideal.subschemeι ≫ P.structureMap) →
        Nonempty (FormalCurveBranch q c p) := by
  sorry

/- Approved generic transversality for the actual trivial P1 family.
Primary source: Laksov-Speiser, Determinantal criteria for transversality
of morphisms, Pacific J.Math.156(2)(1992),307-328, Corollary7.2 p327.
The complement of W in the integral Cartier divisor has codimension at
least two; smooth evaluation preserves codimension and the proper
P1 projection has a proper closed image for this exceptional incidence.
The result asserts the actual pulled-back divisor is etale over C and
that its points lie in W. It does not assert that it is nonempty.
No finite cover, contact structure, line degree, or normalization occurs.
-/
theorem smooth_projectiveLineFamily_transverse_divisor {T Z : Scheme}
    [IsIntegral T] [IsIntegral Z] [CompactSpace T]
    (sT : T ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase)
    [Smooth sT] [Smooth sZ] [IsProper sZ]
    (E : RationalSourceOver P T sT ⟶ Z)
    (hE : E ≫ sZ = pullback.snd P.structureMap sT ≫ sT)
    [Smooth E] [IsDominant E]
    (D : PrimeCartierDivisor Z) (W : Z.Opens)
    (hW : ((D.ideal.support : Set Z) ∩ (W : Set Z)).Nonempty)
    (hDsmooth : Smooth ((D.ideal.subschemeι ⁻¹ᵁ W).ι ≫ D.ideal.subschemeι ≫ sZ)) :
    ∃ V : T.Opens, Dense (V : Set T) ∧
      ∀ t : PointsOver ComplexBase (𝟙 ComplexBase) T sT,
        t.val (IsLocalRing.closedPoint ℂ) ∈ V →
        (∀ p : ProjectiveLine,
          (familyFiber sT t ≫ E) p ∈ D.ideal.support →
            (familyFiber sT t ≫ E) p ∈ W) ∧
        Etale (pullback.fst (familyFiber sT t ≫ E) D.ideal.subschemeι ≫ P.structureMap) := by
  sorry

/- Approved generic normalization of the unique component through a regular
one-dimensional point of an actual finite curve pullback. Sources:
Stacks 0BXR (finite normalization of a locally algebraic scheme),
0C44 / Lemma33.41.2 (normalization is unchanged on the regular locus),
and 0B8X (regular curves over C are smooth). The nonzero image of the
base maximal ideal rules out a vertical component. No ramification
index, power equality, test family, or contact data is an output.
-/
theorem finite_curvePullback_normalization_at_dvr {S Z : Scheme}
    (q : S ⟶ Z) [IsFinite q] (c : ProjectiveLine ⟶ Z)
    (w : (pullback q c : Scheme))
    (hw : IsClosed ({w} : Set (pullback q c : Scheme)))
    [IsDomain ((pullback q c : Scheme).presheaf.stalk w)]
    (hDVR : IsDiscreteValuationRing ((pullback q c : Scheme).presheaf.stalk w))
    (hbase :
      (IsLocalRing.maximalIdeal (ProjectiveLine.presheaf.stalk (pullback.snd q c w))).map
        ((pullback.snd q c).stalkMap w).hom ≠ ⊥) :
    ∃ (C : ComponentNormalization q c) (x : C.curveCover.curve),
      (C.normalization ≫ C.insertion) x = w ∧
      IsClosed ({x} : Set C.curveCover.curve) ∧
      IsIso ((C.normalization ≫ C.insertion).stalkMap x) := by
  sorry

end LeBrunSalamon.StandardInputs

namespace LeBrunSalamon.Construction.Descent.BranchTests

open GenericBranchGeometry LineTests LeBrunSalamon.Refinement
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

local instance : Smooth P.structureMap :=
  smoothProperComplexVariety_smooth (projectiveLineVariety P)

local instance : IsProper P.structureMap := (projectiveLine_smoothProper P).2.1

/-- The formal local model gives ramification on an actual dominating
component normalization.  The ideal exponent is proved in the original
pullback stalk before the normalization is introduced. -/
theorem normalized_ramification {S Z : Scheme} (q : S ⟶ Z) [IsFinite q]
    (c : ProjectiveLine ⟶ Z) (p : ProjectiveLinePoint P)
    (F : FormalCurveBranch q c p) :
    ∃ (C : ComponentNormalization q c) (x : C.curveCover.curve) (e : ℕ),
      RamificationIndex C.curveCover x e ∧ 1 < e := by
  letI : IsLocallyNoetherian (pullback q c : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd q c ≫ P.structureMap)
  let R : Type := (pullback q c : Scheme).presheaf.stalk F.point
  have he : 0 < F.index := lt_trans Nat.zero_lt_one F.greaterThanOne
  obtain ⟨a, _, u, hu⟩ := SheetAlgebra.TransverseBranch.transversePullback_isPowerSeries
    F.index he F.series F.transverse
  let Q : BranchAlgebra.Completion R ≃+* PowerSeries ℂ :=
    F.comparison.trans a.toRingEquiv
  have hQ : Q (algebraMap R (BranchAlgebra.Completion R)
      (((pullback.snd q c).stalkMap F.point).hom F.parameter)) =
      PowerSeries.X ^ F.index * u.val := by
    change a (F.comparison (algebraMap R (BranchAlgebra.Completion R)
      (((pullback.snd q c).stalkMap F.point).hom F.parameter))) = _
    rw [F.parameter_normalized, hu]
  letI : IsDomain R := BranchAlgebra.domain_of_completion Q
  letI : IsDiscreteValuationRing R := BranchAlgebra.dvr_of_completion Q
  have hpower :
      (IsLocalRing.maximalIdeal (ProjectiveLine.presheaf.stalk
        (pullback.snd q c F.point))).map ((pullback.snd q c).stalkMap F.point).hom =
      (IsLocalRing.maximalIdeal ((pullback q c : Scheme).presheaf.stalk F.point)) ^
        F.index :=
    BranchAlgebra.maximalIdeal_image_eq_pow ((pullback.snd q c).stalkMap F.point).hom
      F.parameter F.parameter_generates Q F.index u hQ
  have hbase :
      (IsLocalRing.maximalIdeal (ProjectiveLine.presheaf.stalk
        (pullback.snd q c F.point))).map ((pullback.snd q c).stalkMap F.point).hom ≠ ⊥ :=
    BranchAlgebra.maximalIdeal_image_ne_bot ((pullback.snd q c).stalkMap F.point).hom
      F.parameter F.parameter_generates Q F.index u hQ
  obtain ⟨C, x, hx, hclosed, hiso⟩ :=
    LeBrunSalamon.StandardInputs.finite_curvePullback_normalization_at_dvr
      q c F.point F.closed (show IsDiscreteValuationRing R from inferInstance) hbase
  let f := C.normalization ≫ C.insertion
  letI : IsIso (f.stalkMap x) := hiso
  have hlocal :
      (IsLocalRing.maximalIdeal (ProjectiveLine.presheaf.stalk
        (pullback.snd q c (f x)))).map ((pullback.snd q c).stalkMap (f x)).hom =
      (IsLocalRing.maximalIdeal ((pullback q c : Scheme).presheaf.stalk (f x))) ^
        F.index := by
    exact (show f x = F.point from hx).symm ▸ hpower
  have hn := BranchAlgebra.maximalIdeal_image_comp_of_stalkIso f
    (pullback.snd q c) x F.index hlocal
  have hf : f ≫ pullback.snd q c = C.curveCover.map := by
    simpa only [f, Category.assoc] using C.overLine
  refine ⟨C, x, F.index, ⟨hclosed, he, ?_⟩, F.greaterThanOne⟩
  let Q (g : C.curveCover.curve ⟶ ProjectiveLine) : Prop :=
    (IsLocalRing.maximalIdeal (ProjectiveLine.presheaf.stalk (g x))).map
        (g.stalkMap x).hom =
      (IsLocalRing.maximalIdeal (C.curveCover.curve.presheaf.stalk x)) ^ F.index
  exact (congrArg Q hf).mp hn

/-- A nonzero prime-divisor section has a zero at an actual ordered
pair of complex points of the square. -/
theorem divisor_zero_pair {n : ℕ} (X : ContactFanoManifold n)
    (D : PrimeCartierDivisor (Square X)) :
    ∃ x y : ComplexPoint X.variety,
      pullSection x.map (pullSection (axisFiber y .first) D.sectionValue) = 0 := by
  classical
  let s : Square X ⟶ ComplexBase :=
    firstProjection X.variety.structureMap ≫ X.variety.structureMap
  letI : IsIntegral D.ideal.subscheme := D.integral
  letI : LocallyOfFiniteType (D.ideal.subschemeι ≫ s) := by
    dsimp [s]
    infer_instance
  obtain ⟨z, _⟩ := complexPoint_in_nonempty_open
    (D.ideal.subschemeι ≫ s) ⊤ Set.univ_nonempty
  let q : ComplexBase ⟶ Square X := z.val ≫ D.ideal.subschemeι
  have hq : q ≫ s = 𝟙 ComplexBase := by
    simpa only [q, Category.assoc] using z.property
  let x : ComplexPoint X.variety :=
    ⟨q ≫ firstProjection X.variety.structureMap, by
      simpa only [s, Category.assoc] using hq⟩
  let y : ComplexPoint X.variety :=
    ⟨q ≫ secondProjection X.variety.structureMap, by
      simpa only [s, Category.assoc, firstProjection, secondProjection,
        ← pullback.condition] using hq⟩
  have hxy : x.map ≫ axisFiber y .first = q := by
    apply pullback.hom_ext
    · simp only [axisFiber, firstProjection, Category.assoc, pullback.lift_fst,
        Category.comp_id, x]
    · simp only [axisFiber, secondProjection, Category.assoc, pullback.lift_snd,
        x.overC, Category.id_comp, y]
      rw [← Category.assoc, x.overC, Category.id_comp]
  have hsupport : q (IsLocalRing.closedPoint ℂ) ∈ D.ideal.support := by
    change q (IsLocalRing.closedPoint ℂ) ∈ (D.ideal.support : Set (Square X))
    rw [← D.ideal.range_subschemeι]
    exact ⟨z.val (IsLocalRing.closedPoint ℂ), rfl⟩
  refine ⟨x, y, ?_⟩
  apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff x.map
    (axisFiber y .first) D.sectionValue).2
  rw [hxy]
  by_contra hnonzero
  have hnv := (point_mem_nonvanishing_iff D.line D.sectionValue q).mpr hnonzero
  change q (IsLocalRing.closedPoint ℂ) ∈ (D.ideal.support : Set (Square X)) at hsupport
  rw [D.support_eq] at hsupport
  exact hsupport hnv

/-- The actual evaluation of either two-axis family is over C. -/
theorem axisEvaluation_overC {n : ℕ} {X : ContactFanoManifold n}
    (H : CoveringFamily X) (axis : Axis) :
    H.axisEvaluation axis ≫ firstProjection X.variety.structureMap ≫
      X.variety.structureMap = H.projection ≫ H.parameterToC := by
  have hother : H.otherPoint ≫ X.variety.structureMap =
      H.projection ≫ H.parameterToC := by
    rw [← H.parameter_commutes]
    simp only [parameterToC, Category.assoc, projection_fst_assoc]
  cases axis
  · change H.firstEvaluation ≫ firstProjection X.variety.structureMap ≫
      X.variety.structureMap = _
    rw [firstProjection, pullback.condition]
    simpa only [otherPoint, Category.assoc] using hother
  · change (H.firstEvaluation ≫ swapSelfProduct X.variety.structureMap) ≫
      firstProjection X.variety.structureMap ≫ X.variety.structureMap = _
    rw [Category.assoc, ← Category.assoc (swapSelfProduct X.variety.structureMap),
      swap_first]
    simpa only [otherPoint, Category.assoc] using hother

/-- Positivity chooses one of the two genuine axes.  The transverse
parameter open is then intersected with the actual incidence open for U.
Positive degree forces a divisor intersection on that selected member. -/
theorem transverse_member {n : ℕ} (X : ContactFanoManifold n)
    (hPic : HasPrimitiveContactPicard X.contact) (H : CoveringFamily X)
    (D : PrimeCartierDivisor (Square X)) (W : (Square X).Opens)
    (hW : ((D.ideal.support : Set (Square X)) ∩ (W : Set (Square X))).Nonempty)
    (hDsmooth : Smooth ((D.ideal.subschemeι ⁻¹ᵁ W).ι ≫ D.ideal.subschemeι ≫
      firstProjection X.variety.structureMap ≫ X.variety.structureMap))
    (U : (Square X).Opens) (hU : (U : Set (Square X)).Nonempty) :
    ∃ (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
      (y : ComplexPoint X.variety) (axis : Axis) (p : ProjectiveLinePoint P),
      MeetsOpen (testLine (H.lineAt t) y axis) U ∧
      testLine (H.lineAt t) y axis (p.map (IsLocalRing.closedPoint ℂ)) ∈ D.ideal.support ∧
      testLine (H.lineAt t) y axis (p.map (IsLocalRing.closedPoint ℂ)) ∈ W ∧
      Etale (pullback.fst (testLine (H.lineAt t) y axis) D.ideal.subschemeι ≫
        P.structureMap) := by
  classical
  letI : IsIntegral (Square X) := square_integral (X := X)
  let s : Square X ⟶ ComplexBase :=
    firstProjection X.variety.structureMap ≫ X.variety.structureMap
  letI : Smooth s := by dsimp [s]; infer_instance
  letI : IsProper s := by dsimp [s]; infer_instance
  obtain ⟨x₀, y₀, hzero⟩ := divisor_zero_pair X D
  obtain ⟨axis, hpositive⟩ := LineTests.twoAxis_positive_degree H hPic D.line D.sectionValue
    D.nonzero x₀ y₀ hzero
  let E : RationalSourceOver P H.Parameter H.parameterToC ⟶ Square X :=
    H.sourceProductIso.inv ≫ H.axisEvaluation axis
  letI : Smooth E := by dsimp [E]; infer_instance
  letI : IsDominant (H.axisEvaluation axis) := ⟨H.axisEvaluation_dominant axis⟩
  letI : IsDominant E := by dsimp [E]; infer_instance
  have hE : E ≫ s = pullback.snd P.structureMap H.parameterToC ≫ H.parameterToC := by
    dsimp [E, s]
    rw [Category.assoc, axisEvaluation_overC, ← Category.assoc]
    simp only [sourceProductIso, IsPullback.isoPullback_inv_snd]
  obtain ⟨V, hVdense, hV⟩ :=
    LeBrunSalamon.StandardInputs.smooth_projectiveLineFamily_transverse_divisor
      H.parameterToC s E hE D W hW hDsmooth
  let J : H.Parameter.Opens := H.meetingOpen axis U ⊓ V
  have hJ : (J : Set H.Parameter).Nonempty :=
    hVdense.inter_open_nonempty _ (H.meetingOpen axis U).isOpen
      (LineTests.meetingOpen_nonempty H axis U hU)
  obtain ⟨w, hw⟩ := complexPoint_in_nonempty_open H.parameterToC J hJ
  let t := H.memberOfParameter w
  let y := H.otherOfParameter w
  have hparameter : H.parameterPoint t y = w := LineTests.parameterPoint_decompose H w
  have hcurve : GenericBranchGeometry.familyFiber H.parameterToC w ≫ E =
      testLine (H.lineAt t) y axis := by
    rw [← hparameter]
    change H.productFiber t y ≫ (H.sourceProductIso.inv ≫ H.axisEvaluation axis) = _
    rw [← Category.assoc, productFiber_inclusion, fiberInclusion_evaluation]
  have hmeets : MeetsOpen (testLine (H.lineAt t) y axis) U := by
    apply LineTests.meets_of_mem_meetingOpen H t y axis U
    rw [hparameter]
    exact hw.1
  obtain ⟨havoid, htransverse⟩ := hV w hw.2
  rw [hcurve] at havoid htransverse
  obtain ⟨p, hp⟩ := positive_degree_exists_zero
    (pullbackLine (testLine (H.lineAt t) y axis) D.line) (hpositive t y)
      (pullSection (testLine (H.lineAt t) y axis) D.sectionValue)
  have hsupport : testLine (H.lineAt t) y axis
      (p.map (IsLocalRing.closedPoint ℂ)) ∈ D.ideal.support := by
    change testLine (H.lineAt t) y axis (p.map (IsLocalRing.closedPoint ℂ)) ∈
      (D.ideal.support : Set (Square X))
    rw [D.support_eq]
    intro hnv
    have hpull : pullSection (p.map ≫ testLine (H.lineAt t) y axis) D.sectionValue ≠ 0 :=
      (point_mem_nonvanishing_iff D.line D.sectionValue
        (p.map ≫ testLine (H.lineAt t) y axis)).mp
          (by
            change testLine (H.lineAt t) y axis (p.map (IsLocalRing.closedPoint ℂ)) ∈
              (nonvanishingOpen D.line D.sectionValue : Set (Square X))
            exact hnv)
    exact hpull ((FullFamilyDiagonalProof.pullSection_comp_zero_iff p.map
      (testLine (H.lineAt t) y axis) D.sectionValue).1 hp)
  exact ⟨t, y, axis, p, hmeets, hsupport,
    havoid (p.map (IsLocalRing.closedPoint ℂ)) hsupport, htransverse⟩

end LeBrunSalamon.Construction.Descent.BranchTests

namespace LeBrunSalamon.Construction.Descent

open LeBrunSalamon.Refinement

/-- SOURCE des:branch-model through des:pullback-germ. The proof must
choose a transverse contact line of one of the TWO types, avoid the bad
codimension-two set, and identify the smooth pullback germ before taking
its normalization. No assertion that arbitrary line pullbacks are normal. -/
theorem ramifiedTest_exists {n : ℕ} (X : ContactFanoManifold n)
    (hPic : HasPrimitiveContactPicard X.contact) {D : ProperPair X}
    {I : FiniteValueImage D} (N : NormalizedImage I) (U : GoodOpen N)
    (H : CoveringFamily X) (h : ¬ EtaleInCodimensionOne N.cover.map) :
    Nonempty (RamifiedTest N U H) := by
  classical
  letI : IsIntegral (Square X) := LineTests.square_integral (X := X)
  letI : IrreducibleSpace N.cover.source := N.cover.integral.1
  letI : AlgebraicGeometry.IsReduced N.cover.source := ⟨N.cover.integral.2⟩
  letI : IsIntegral N.cover.source :=
    isIntegral_of_irreducibleSpace_of_isReduced N.cover.source
  letI : IsDominant N.cover.map := ⟨N.cover.dominant⟩
  let s : Square X ⟶ ComplexBase :=
    firstProjection X.variety.structureMap ≫ X.variety.structureMap
  letI : Smooth s := by dsimp [s]; infer_instance
  letI : IsProper s := by dsimp [s]; infer_instance
  unfold EtaleInCodimensionOne at h
  push_neg at h
  obtain ⟨r, hr, hnot⟩ := h
  obtain ⟨B, W, _, hW, hBsmooth, hmodel⟩ :=
    LeBrunSalamon.StandardInputs.finite_normal_branch_divisor_formalModel
      s N.cover.map N.cover.normal r hr hnot
  obtain ⟨t, y, axis, p, hmeets, hB, hpW, htransverse⟩ :=
    BranchTests.transverse_member X hPic H B W hW hBsmooth U.openSet U.dense.nonempty
  have hcurve : testLine (H.lineAt t) y axis ≫ s = P.structureMap := by
    cases axis <;>
      simp only [testLine, s, firstProjection, Category.assoc,
        pullback.lift_fst_assoc, pullback.lift_fst, (H.lineAt t).curve.overC,
        y.overC, Category.comp_id]
  obtain ⟨F⟩ := hmodel (testLine (H.lineAt t) y axis) hcurve p hB hpW htransverse
  obtain ⟨C, x, e, he, he1⟩ := BranchTests.normalized_ramification N.cover.map
    (testLine (H.lineAt t) y axis) p F
  exact ⟨{
    member := t
    otherPoint := y
    axis := axis
    meets := hmeets
    component := C
    ramifiedPoint := x
    index := e
    ramification := he
    ramified := he1 }⟩

end LeBrunSalamon.Construction.Descent

namespace LeBrunSalamon.Refinement

open LeBrunSalamon.Construction

/-- SOURCE des:descent, specialized to a proper integral SCHEME. The proof must supply simple
connectedness and the free covering line family from the contact-Fano/primitive hypotheses, then run ALL-
sheet and branch tests. This is a manuscript claim to prove, not a general proper-descent theorem. -/
theorem contactValueDescent_obligation {n : ℕ} (X : ContactFanoManifold n)
    (hPic : HasPrimitiveContactPicard X.contact) (D : ProperPair X) :
    ∃! B : ExternalSquareSections X.variety X.contact.sequence.line, D.DescendsTo B := by
  classical
  obtain ⟨L⟩ := Lines.coveringFamily_exists X hPic
  obtain ⟨I⟩ := Descent.finiteValueImage_exists D
  obtain ⟨N⟩ := Descent.normalizedImage_exists I
  obtain ⟨U⟩ := Descent.goodOpen_exists N
  have hs := Descent.allSheets_split D I N U L
  have hc : Descent.EtaleInCodimensionOne N.cover.map := by
    by_contra h
    obtain ⟨R⟩ := Descent.ramifiedTest_exists X hPic N U L h
    exact Descent.allSheets_exclude_ramifiedTest hs R
  have hi := Descent.finiteEtale_contactSquare_trivial X N.cover
    (Descent.purity_over_contactSquare N.cover hc)
  obtain ⟨B, hB⟩ := Descent.finiteImage_graph_recovers_section D I N hi
  refine ⟨B, hB, ?_⟩
  intro C hC
  exact D.descent_unique hC hB

end LeBrunSalamon.Refinement

end

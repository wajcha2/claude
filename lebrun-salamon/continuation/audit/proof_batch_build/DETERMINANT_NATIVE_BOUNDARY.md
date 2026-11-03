# Repaired contact determinant: native dependency boundary

The audit of `LeBrunSalamon.PhaseTwentySeven.contact_distribution_determinant` passed the pinned stock compiler with exit code zero in 36.045 seconds. It imports the already compiled repaired Part05A, whose actual candidate SHA-256 remains `7e6497b17a33f6b700418f118b45624833c7f8407a989e685813cb648fe9cf05` and matches its successful compilation receipt.

**Scope:** recovered baseline dependency interfaces. This audit does not certify the current cumulative dependency cone. No source theorem was changed, no admission was added, and the earlier first-jet evidence was preserved.

## Method and results

The validated breadth-first walker traversed every loaded constant's type, theorem/definition/opaque value when available, and inductive constructors. Nonproject constants were traversed, not skipped. The reported routes are shortest dependency paths.

| Item | Result |
| --- | ---: |
| All constants visited | 41995 |
| Project constants visited | 631 |
| Direct uses of `sorryAx` | 5 |
| Missing constants | 0 |
| Custom project axioms | 0 |

## The false original input is absent

Native check:

```text
OLD_FALSE_PUBLISHED_INPUT name=LeBrunSalamon.PublishedInputs.Step3e.symplecticDeterminant present_in_environment=false present_in_closure=false
```

The retained `PhaseTwentySeven.symplecticDeterminant` name is the new proved wrapper, whose native printed type explicitly includes alternation. The contact theorem reaches the new alternating-discriminant leaf through that wrapper. The exact wrapper type is also preserved in `DETERMINANT_DEPENDENCY_NATIVE_OUTPUT.txt` and `DETERMINANT_DEPENDENCY_SUMMARY.json`.

## The five direct admitted leaves

There is one repaired discriminant leaf and four inherited generic geometry/sheaf leaves:

1. `PublishedInputs.Step3e.alternatingDiscriminantTrivial`: the explicitly alternating perfect form has trivial discriminant line on the specified smooth proper connected complex base.
2. `PublishedInputs.SheafFunctoriality.exterior_locallyFree`: an exterior power of a rank-d locally free module has rank `d.choose r`.
3. `PhaseTwentyFive.smooth_cotangent_rank`: smooth relative dimension d gives a locally free rank-d cotangent module.
4. `PublishedInputs.SheafFunctoriality.exteriorPresentation`: existence of the project's universal exterior-sheaf presentation.
5. `PublishedInputs.SheafFunctoriality.cotangentPresentation`: existence of the project's universal cotangent-sheaf presentation.

The audit identifies these actual imported declarations; it does not silently upgrade their publication eligibility. Their exact native types and shortest paths follow.

```text
DIRECT_SORRY LeBrunSalamon.PublishedInputs.Step3e.alternatingDiscriminantTrivial
MODULE RecompileBasePart05A
SHORTEST_PATH LeBrunSalamon.PhaseTwentySeven.contact_distribution_determinant -> LeBrunSalamon.PhaseTwentySeven.symplecticDeterminant -> LeBrunSalamon.PublishedInputs.Step3e.alternatingDiscriminantTrivial
TYPE ∀ {X : AlgebraicGeometry.Scheme.{0}} {n : ℕ} (s : Quiver.Hom.{0, 1} X LeBrunSalamon.PhaseOne.ComplexBase)
  [AlgebraicGeometry.Smooth.{0} s] [AlgebraicGeometry.IsProper.{0} s] [ConnectedSpace.{0} ↥X]
  (E : LeBrunSalamon.PhaseOne.AlgebraicVectorBundle X (HMul.hMul.{0, 0, 0} 2 n))
  (L : LeBrunSalamon.PhaseOne.LineBundle X)
  (b : Quiver.Hom.{0, 1} (LeBrunSalamon.PhaseTwentyFive.tensorSheaf E.sheaf E.sheaf) L.sheaf),
  CategoryTheory.IsIso.{0, 1} (LeBrunSalamon.PhaseTwentyFive.currySheaf b) →
    (∀ (U : AlgebraicGeometry.Scheme.Opens.{0} X) (u : LeBrunSalamon.PhaseTwentyFive.SectionsOn.{0} E.sheaf U),
        Eq.{1}
          ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (AlgebraicGeometry.Scheme.Modules.Hom.app.{0} b U))
            (((LeBrunSalamon.PhaseTwentyFive.SheafBilinearMap.apply.{0}
                  (LeBrunSalamon.PhaseTwentyFive.tensorPresentation E.sheaf E.sheaf).pair U)
                u)
              u))
          0) →
      Nonempty.{1}
        (CategoryTheory.Iso.{0, 1}
          (LeBrunSalamon.PhaseTwentySix.tensorLine
              (LeBrunSalamon.PhaseTwentySix.linePower (LeBrunSalamon.PhaseTwentySix.dualLine L) n)
              (LeBrunSalamon.PhaseTwentySix.determinantLine E)).sheaf
          (LeBrunSalamon.PhaseTwentySix.trivialLine X).sheaf)
```

```text
DIRECT_SORRY LeBrunSalamon.PublishedInputs.SheafFunctoriality.exterior_locallyFree
MODULE RecompileBasePart04
SHORTEST_PATH LeBrunSalamon.PhaseTwentySeven.contact_distribution_determinant -> LeBrunSalamon.PhaseTwentySix.determinantLine -> LeBrunSalamon.PhaseTwentySix.determinantLine._proof_1 -> LeBrunSalamon.PhaseTwentySix.exteriorSheaf_locallyFree -> LeBrunSalamon.PublishedInputs.SheafFunctoriality.exterior_locallyFree
TYPE ∀ {X : AlgebraicGeometry.Scheme.{0}} {E : LeBrunSalamon.PhaseOne.OModule.{0} X} {d : ℕ},
  LeBrunSalamon.PhaseOne.IsLocallyFreeOfRank E d →
    ∀ (r : ℕ),
      LeBrunSalamon.PhaseOne.IsLocallyFreeOfRank (LeBrunSalamon.PhaseTwentySix.exteriorSheaf.{0} E r) (d.choose r)
```

```text
DIRECT_SORRY LeBrunSalamon.PhaseTwentyFive.smooth_cotangent_rank
MODULE RecompileBasePart04
SHORTEST_PATH LeBrunSalamon.PhaseTwentySeven.contact_distribution_determinant -> LeBrunSalamon.PhaseTwentyFive.intrinsicTangentBundle -> LeBrunSalamon.PhaseTwentyFive.intrinsicTangentBundle._proof_1 -> LeBrunSalamon.PhaseTwentyFive.smooth_tangent_rank -> LeBrunSalamon.PhaseTwentyFive.smooth_cotangent_rank
TYPE ∀ {X S : AlgebraicGeometry.Scheme.{0}} (s : Quiver.Hom.{0, 1} X S) (d : ℕ),
  AlgebraicGeometry.SmoothOfRelativeDimension.{0} d s →
    LeBrunSalamon.PhaseOne.IsLocallyFreeOfRank (LeBrunSalamon.PhaseTwentyFive.cotangentSheaf.{0} s) d
```

```text
DIRECT_SORRY LeBrunSalamon.PublishedInputs.SheafFunctoriality.exteriorPresentation
MODULE RecompileBasePart04
SHORTEST_PATH LeBrunSalamon.PhaseTwentySeven.contact_distribution_determinant -> LeBrunSalamon.PhaseTwentySix.determinantLine -> LeBrunSalamon.PhaseTwentySix.exteriorSheaf -> LeBrunSalamon.PhaseTwentySix.exteriorPresentation -> LeBrunSalamon.PhaseTwentySix.exteriorPresentation_exists -> LeBrunSalamon.PublishedInputs.SheafFunctoriality.exteriorPresentation
TYPE ∀ {X : AlgebraicGeometry.Scheme.{u_1}} (E : LeBrunSalamon.PhaseOne.OModule.{u_1} X) (r : ℕ),
  Nonempty.{u_1 + 2} (LeBrunSalamon.PhaseTwentySix.ExteriorPresentation.{u_1} E r)
```

```text
DIRECT_SORRY LeBrunSalamon.PublishedInputs.SheafFunctoriality.cotangentPresentation
MODULE RecompileBasePart04
SHORTEST_PATH LeBrunSalamon.PhaseTwentySeven.contact_distribution_determinant -> LeBrunSalamon.PhaseTwentyFive.intrinsicTangentBundle -> LeBrunSalamon.PhaseTwentyFive.tangentSheaf -> LeBrunSalamon.PhaseTwentyFive.cotangentSheaf -> LeBrunSalamon.PhaseTwentyFive.cotangentPresentation -> LeBrunSalamon.PhaseTwentyFive.cotangentPresentation_exists -> LeBrunSalamon.PublishedInputs.SheafFunctoriality.cotangentPresentation
TYPE ∀ {X S : AlgebraicGeometry.Scheme.{u_1}} (s : Quiver.Hom.{u_1, u_1 + 1} X S),
  Nonempty.{u_1 + 2} (LeBrunSalamon.PhaseTwentyFive.CotangentPresentation.{u_1} s)
```

## Evidence files

- Executed source: `LSSymplecticDeterminantDependencyAudit.lean`.
- Receipt and unmodified compiler logs: `LSSymplecticDeterminantDependencyAudit/`.
- Machine-readable summary: `DETERMINANT_DEPENDENCY_SUMMARY.json`.
- Full native output: `DETERMINANT_DEPENDENCY_NATIVE_OUTPUT.txt`.
- All 631 project declaration names: `DETERMINANT_PROJECT_CLOSURE.txt`.
- Final driver status: `DETERMINANT_CLOSURE_RUN_STATUS.json`.

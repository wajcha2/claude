# LeBrun–Salamon formalisation — Step 2 statement audit

**Date:** 1 November 2026  
**Verdict:** **STEP 2 PASSED**

## Critical finding

The theorem exported by the Step 1 strict tree was not the complete theorem targeted by the pinned manuscript. It had the geometric hypotheses and concluded only

```lean
IsLocallyRiemannianSymmetric n M
```

that is, the intrinsic equation `∇Rm = 0`. The pinned Riemannian statement also says that the metric is homothetic, after multiplication by a positive constant, to an actual compact symmetric positive quaternionic–Kähler Wolf space. Merely calling the source “locally symmetric” does not expose that target, the homothety, or the positive scaling.

The Step 2 proposition therefore strengthens the conclusion. It does not introduce a contact-Fano, twistor, classification, `ProjectInputs`, or other proof-package assumption.

## Frozen statement

For a smooth Riemannian manifold `M` modelled on `R^(4*n)`, the proposition is

```lean
def LeBrunSalamonStatement (n : ℕ) (M : Type u) ... : Prop :=
  2 ≤ n →
  IsPositiveQuaternionicKahler n M →
    IsLocallyRiemannianSymmetric n M ∧
      Nonempty (WolfHomothety (closedRiemannianSpace n M))
```

The future exported theorem must have precisely this mathematical content. The file includes `leBrunSalamonStatement_iff`, proved by `Iff.rfl`, to make accidental strengthening or weakening easy to detect.

## Clause-by-clause audit

| Mathematical clause | Frozen Lean encoding | Verdict |
|---|---|---|
| Real dimension `4n` | `Model n := EuclideanSpace ℝ (Fin (4*n))` | Exact. |
| Higher-dimensional range | `2 ≤ n` | Exact for real dimension at least eight. |
| Dimension four | Excluded | Correct: the parallel rank-three formulation alone is not the standard four-dimensional self-dual Einstein definition. |
| Smooth, without boundary | `IsManifold (model n) ∞ M`, with `modelWithCornersSelf` | Correct boundaryless encoding. |
| Closed | `CompactSpace M` plus the boundaryless model | Correct; compactness supplies completeness in the intended finite-dimensional Riemannian setting, so no extra completeness assumption is inserted. |
| Connected and inhabited | `ConnectedSpace M`, `Nonempty M` | Correct and nonvacuous. |
| Riemannian metric | mathlib Riemannian bundle, smooth metric, and intrinsic Riemannian distance instances | Correct statement-level data. |
| Quaternionic–Kähler | a locally framed quaternionic rank-three subbundle of `End(TM)`, parallel for the Levi–Civita connection | The standard intrinsic formulation for `n ≥ 2`; equivalence with holonomy containment is an explicit bridge obligation. |
| Positive scalar curvature | contraction of the actual Levi–Civita curvature in an orthonormal basis | Correct sign-sensitive target; curvature identification and basis independence must be proved internally. |
| Parallel curvature | `IsLocallyRiemannianSymmetric n M` | Exact intrinsic `∇Rm = 0` conclusion. |
| Homothety | smooth equivalence with smooth inverse and `f* g_target = scale · g_source`, `scale > 0` | Exact; the scale multiplies the metric tensor. |
| Wolf space | an actual compact, connected, simply connected, positive quaternionic–Kähler globally symmetric Riemannian space | Correct intrinsic Wolf class, not a bare name or Boolean label. |
| Source simply connected | Not assumed | Correct. It is a consequence of the conclusion/known positive-QK theory, not a hypothesis of the conjecture. |

## Why the previous statement was insufficient

The former theorem proves the first projection of the new conclusion. The new source contains the admission-free lemma

```lean
theorem exactStatement_implies_parallelCurvature ... :
    IsLocallyRiemannianSymmetric n M
```

The converse is deliberately absent: turning `∇Rm = 0` into a specified Wolf target uses global topology and the classification of compact symmetric positive quaternionic–Kähler spaces.

## Definition-validation obligations

The proposition compiles, but final mathematical certification also requires proving that the operational definitions coincide with the standard textbook notions. These are downstream proof obligations, not hidden assumptions:

1. smooth endomorphism fields used in the local-frame predicate agree with smooth sections of the endomorphism bundle;
2. for `n ≥ 2`, a Levi–Civita-parallel local quaternionic three-plane field agrees with holonomy containment in `Sp(n)Sp(1)`;
3. the commutator formula used for `IsLeviCivitaCurvature` gives the actual Riemann tensor with the recorded sign convention;
4. smooth tangent fields extend prescribed tangent vectors locally/globally as needed, making the curvature witness unique;
5. the scalar contraction is independent of orthonormal basis and agrees with scalar curvature;
6. `IsParallelCurvature` agrees with the tensor equation `∇Rm = 0`;
7. the point-symmetry structure agrees with the usual globally Riemannian symmetric-space condition;
8. Wolf’s classification identifies the intrinsic target class with the standard homogeneous Wolf-space list.

Routine transports, specialisations, coercion identities, and equivalence directions specific to this formalisation must be proved in Lean. A `sorry` is permitted only for an exact theorem from the literature under the project’s published-input policy.

## Mechanical verification

- Checked-in source SHA-256: `9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296`.
- Lean: `v4.36.0-rc1`, commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`.
- mathlib: `116662aa4c1e9106ab5c609b3214b02f6e11a65a`.
- GitHub Actions run: `41305229872`.
- Compilation return code: `0`.
- Generated olean SHA-256: `48c594a66e4e43de69190cf35994405172f04cfa479242cbdb965f129f12080b`.
- `sorry` tokens: `0`.
- `admit` tokens: `0`.
- custom `axiom` declarations: `0`.
- opaque declarations: `0`.

## Step 2 gate

- [x] Standard and pinned formulations compared critically.
- [x] Incomplete legacy conclusion identified.
- [x] Exact dimension range frozen.
- [x] Closedness, connectedness, and nonemptiness explicit.
- [x] No erroneous four-dimensional formulation included.
- [x] Source simple connectedness not added as a hypothesis.
- [x] Both `∇Rm = 0` and actual Wolf-space homothety included.
- [x] No project-specific proof input occurs in the proposition.
- [x] Statement layer has no admissions or custom axioms.
- [x] Checked-in source compiles unchanged under the frozen toolchain.

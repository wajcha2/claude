# OBL-056 progress addendum — 4 November 2026

**The ordinary test-centre construction is now proved. OBL-056 remains open.** This adds a completed result after `OBL056_PROGRESS_20261104.md`; the original plan and that earlier note remain unchanged, with their earlier status preserved as history.

`LSResiduePointLiftingV2.lean` imports only Mathlib. Its seven declarations completed a full local check in **29.762 s**, with return code 0, no errors, a complete output, and unchanged source/runtime/import guards. All seven axiom queries contain only the standard axioms. No published input or project hypothesis was introduced.

For an arbitrary scheme morphism `f : T → X`, a point `t : T`, a field `K`, and an actual point `p : Spec K → X`, assume exactly:

- `f.residueFieldMap t` is an isomorphism;
- `p(closedPoint K) = f(t)`.

The definition `residuePointLift` uses the inverse of this actual residue map, the explicit transport along the supplied point equality, and the canonical residue-field embedding of `p`. It proves the literal equations

```
q ≫ f = p
q(closedPoint K) = t.
```

For a structural square `f ≫ s = sT` and `p ≫ s = b`, it also proves `q ≫ sT = b`. No Artinianity, flatness, smoothness, properness, or residue-field isomorphism for `p` is required.

The public helper `LeBrunSalamon.Next3i.ResiduePointLifting.exists_localTestCentre` specializes this construction to `T = Spec B` for an arbitrary commutative local ring `B`, using its actual closed point. Given the literal residue-isomorphism, centre and structural data in the intended 02HX test, it supplies the actual `i : Spec K → Spec B`, the equality `i ≫ alpha = p`, the correct closed-point image, and the base equation. For `K = ℂ`, these are precisely the point data taken as hypotheses by the completed family-restriction and central-coefficient lemmas.

This completes the **ordinary construction** left pending under boundary 1 in the earlier note. It does not install the proposed 02HX criterion or prove that every test lifts through a small extension. The flat source-family ideal comparison, the actual internal-Hom/dual/tensor/pushforward coefficient comparison, and the support/cohomology argument remain open. Both proposed generic published inputs remain proposals; the original OBL-056 proof is unchanged and receives no credit.

The source SHA256 is `53da8dfb3645f25aabb232910ab67e2913451367ddda02c265ed59062582fa7c`; the checked diagnostic output is `d9b6db33a867241bbd68083258c276af18612fbe9b58785da0bdf578d71fa9e6`. Root independently read all seven declarations and confirmed the inverse-residue-map direction, point-equality transport, canonical residue-point factorization, and exact composite/centre/base equations. The complete 19-file evidence preserves the initial failed attempt and its narrow repairs. These are local diagnostic results, with no stock native acceptance claimed for this isolated module.

Exact source, profile, review and full evidence blobs are indexed by `RESIDUE_POINT_LIFTING_HANDOFF.json`. `OBL056_PROGRESS_20261104_RESIDUE_ADDENDUM.json` binds this addendum, the historical note, the successful receipt, and root's independent source review.

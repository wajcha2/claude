# LeBrun–Salamon cumulative recovery source through Step 3g (pre-kernel checkpoint)

This directory is a loss-prevention mirror of the cumulative source checkpoint saved in the ChatGPT Library on 2026-11-03.

## Reconstruction

```bash
cat archive.b64.part-* | base64 -d > LeBrunSalamon_Cumulative_Precompile_Step3g_V2_20261103.zip
sha256sum -c PACKAGE.sha256
unzip -t LeBrunSalamon_Cumulative_Precompile_Step3g_V2_20261103.zip
```

The archive contains the 129-module cumulative source tree, the Step 3e and Step 3g source transformations, the source and admission manifests, the exact build order, and the resumable kernel-build script.

The exact Lean environment is Lean `v4.36.0-rc1` with mathlib commit `116662aa4c1e9106ab5c609b3214b02f6e11a65a`.

This is a **pre-kernel** recovery checkpoint. Final Step 3g certification records are added separately after the cumulative replay passes.

The prior all-files preservation archive is stored in the Library at `/Lean formalization checkpoints/LeBrunSalamon_Preservation_Steps1_2_3a_3f_20261102.zip`, SHA-256 `c7fd95263b4e10ddc947e6ddc80013623dc044f7ab14f04a157c6dfe9e0e2e59`.

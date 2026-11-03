# Full committed-source CI replay: 41728791345

The stock pinned compiler replay of commit `6fa6ee1a25735be73e73be455aed94ad88eae8e1` finished with failure on 3 November 2026 at 22:29:04 UTC. It selected all 149 project modules with the 12,000 MiB Lean allocation cap.

The run accepted 29 modules: 12 outputs strictly reused from run 41714131927 after source, runtime and complete dependency validation, and 17 newly compiled outputs. One module failed and 119 were blocked by dependency failure. The final replay revalidated all 29 accepted modules and found no changed sources, dependency artifacts, or runtime files.

The sole compiler error is in `LSPublishedPicard.lean`, line 18: `structureModule` is not in scope. Its definition is `LeBrunSalamon.PhaseTwentyFive.structureModule`; this is a name-resolution integration error. No output or proof acceptance is inferred for the blocked modules, including RecompileSections and RecompileExtensionsPart01.

Freshly accepted modules include RecompileBasePart04, RecompileBasePart05A, RecompileBasePart05B, RecompileBasePart05C, RecompileBasePart06, RecompileBasePart07, and their newly imported helper modules. The accepted output set and exact diagnostics are recorded in `CI_RECEIPT.json`, `RUN_STATUS.json`, and `ERRORS.json`.

The downloaded artifact is 15,234,944 bytes with SHA-256 `4be2f7267d42f0574499175028a4ee195c1f9eb1535a0f531c37c545d2cafce0`. Every accepted source, direct import, project/external dependency output, compiler/library fingerprint, output artifact, diagnostic log, and reuse provenance was validated against the committed snapshot. `VALIDATED_SEEDS.json` additionally filters this evidence against the live working source tree at its recorded timestamp: 28 modules still match with their entire ancestry; the later LSAffineDerivations edit is excluded.

This run does not establish acceptance of Steps 3c–3g or the published-theorem-only milestone. The live working tree has subsequent candidate proof changes and is distinct from this immutable CI source snapshot.

Run: https://github.com/wajcha2/claude/actions/runs/41728791345

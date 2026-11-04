# Early smoothing closure — CI41769360325

The immutable commit `d660456c481c27fcd49666f306222521034f1616` selected the120-module ancestry of `LSSmoothingAssembly`. The independently verified result is116 accepted,1 failed,3 blocked:115 prior cached outputs and one fresh native pass for `LSScaledVelocities` in12.297s.

`LSVelocityAdditionFamily` finished with nine concrete Lean diagnostics in96.966s. They concern names and explicit categorical/scalar carriers, plus a tensor-product finite-type instance search. `LSScaledVelocityDifferential`, `LSSuitablePair` and `LSSmoothingAssembly` were blocked. This is a completed compiler failure, not a900-second wall-clock timeout. The complete diagnostics are preserved in ERRORS.json and the original logs.

The artifact ZIP hash `707793be45308f2c9e4b9229f7dab282e492e2eda082cda020ff172fd33eaf4b` matches GitHub. Source bytes were bound independently to the actual commit tree. Compiler/runtime identities, imports, dependency artifacts, recursive ancestry, outputs and logs were validated; final validation found no changed input or runtime and no invalidation. All116 accepted outputs matched the live sources at collection.

This early stage does not contain `LSConicJets` and is not a full-graph result. It provides no additional accepted obligation while the original Point1 reverse-dependency gate remains open. The full268-module replay continues separately.

Run: https://github.com/wajcha2/claude/actions/runs/41769360325

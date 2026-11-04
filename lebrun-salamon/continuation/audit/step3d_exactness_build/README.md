# Actual vector-bundle pullback and fiber exactness

Both proof candidates passed the pinned native compiler in the isolated, verified historical interface recorded in SUMMARY.json. An exhaustive traversal of constant types, values and constructors found exactly one direct admitted theorem for each root: the original local splitting theorem of EGA I, chapitre 0, (5.4.9), printed p.52. No old project pullback/fiber exactness admission, missing constant or custom project axiom occurs in either checked closure.

The pullback proof transports the original local retractions through restriction and actual pullback-composition comparisons, proves monicity by the sheaf axiom, and combines it with the left adjoint's right exactness. The fiber proof uses an actual finite free frame on Spec C to prove quasi-coherence, then proves injection, surjection and range/kernel equality for the original global-section maps.

LSVectorBundlePullback was copied byte-for-byte from the passing source. The checked fiber body was inserted after the existing FiberRankProof in Ext02; Ext02 and Ext03 retain their original public theorem types. Their complete containing modules and current reverse-dependency cone must still be replayed. These helper passes do not certify full Step 3d or milestone acceptance.

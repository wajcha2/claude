import RecompileBasePart06
import Lean.Util.CollectAxioms

/-! Generated audit only. Not a production module or an additional obligation.
Native output is authoritative only with its exact receipt and parent contexts. -/
open Lean Elab Command
set_option pp.all true
set_option pp.maxSteps 10000000

run_cmd do
  let env := (← getEnv).setExporting false
  let moduleFor (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  for root in #[
    ``LeBrunSalamon.PhaseThirty.openImmersion_cotangentMap_isIso
  ] do
    let some ci := env.checked.get.find? root | throwError m!"Missing audit constant {root}"
    logInfo m!"CI_SIGNATURE {root}
LEVEL_PARAMS {String.intercalate "," (ci.levelParams.map Name.toString)}
MODULE {moduleFor root}
TYPE {ci.type}"
  logInfo "CI_SIGNATURES_COMPLETE"

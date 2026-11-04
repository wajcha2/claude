import LSVectorBundlePullback
import LSFiniteFreeHomBaseChange
import LSSectionBundleAdapters
import LSGeneratingUnitOpensAdapter
import Lean
open Lean Elab Command
set_option pp.universes true
set_option pp.fullNames true
run_cmd do
  let env := (← getEnv).setExporting false
  for n in #[``LeBrunSalamon.PublishedInputs.BaseChangeFibers.vectorBundle_pullback_shortExact,
      ``LeBrunSalamon.VectorBundlePullback.vectorBundle_pullback_shortExact,
      ``LeBrunSalamon.PublishedInputs.BaseChangeFibers.homBaseChange_isIso,
      ``LeBrunSalamon.FiniteFreeHomBaseChange.homComparison_isIso,
      ``LeBrunSalamon.PublishedInputs.BaseChangeFibers.generating_sections_unitOpen,
      ``LeBrunSalamon.GeneratingUnitOpensAdapter.generating_sections_unitOpen,
      ``LeBrunSalamon.Construction.Descent.totalLine_exists,
      ``LeBrunSalamon.SectionBundleAdapters.totalLine_exists,
      ``LeBrunSalamon.PublishedInputs.BaseChangeFibers.totalBundle_representation,
      ``LeBrunSalamon.SectionBundleAdapters.totalBundle_representation] do
    let some ci := env.checked.get.find? n | throwError m!"Missing {n}"
    logInfo m!"SIGNATURE {n} LEVELS {ci.levelParams} TYPE {ci.type}"

import Lean

set_option Elab.async false
set_option stderrAsMessages false

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "MODEL_DIFFERENTIAL_FLUSH_SMOKE_RAW_STDERR"
  err.flush

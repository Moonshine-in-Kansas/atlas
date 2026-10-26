import Atlas
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let input ← IO.FS.readFile "verification/status-audit/2026-09-14/range-parents.txt"
  let h ← IO.FS.Handle.mk "verification/status-audit/2026-09-14/range-modules.tsv" IO.FS.Mode.write
  for s in input.splitOn "\n" do
    if s.isEmpty then continue
    let n := s.toName
    let some idx := env.getModuleIdxFor? n | continue
    h.putStrLn (s ++ "\t" ++ env.allImportedModuleNames[idx.toNat]!.toString)
  h.flush

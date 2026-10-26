import Export
open Lean

def main (args : List String) : IO Unit := do
  let [modulesFile, inventoryFile] := args
    | throw <| IO.userError "Expected module list and inventory path"
  initSearchPath (← findSysroot)
  let modules := (← IO.FS.readFile modulesFile).splitOn "\n" |>.filter (· != "")
  let imports := modules.toArray.map fun s => { module := s.toName : Import }
  let env ← importModules imports {}
  let mut roots : Array Name := #[]
  let inventory ← IO.FS.Handle.mk inventoryFile .write
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.allImportedModuleNames[idx.toNat]!.toString
    unless mod == "Atlas" || mod.startsWith "Atlas." do continue
    let excluded := info.isUnsafe
    inventory.putStrLn <| Json.compress <| Json.mkObj [
      ("declaration", toJson name.toString), ("module", toJson mod),
      ("unsafe_excluded", toJson excluded), ("theorem", toJson info.isTheorem)]
    unless excluded do roots := roots.push name
  inventory.flush
  if roots.isEmpty then throw <| IO.userError "Empty ATLAS inventory"
  (← IO.getStderr).putStrLn s!"Exporting {roots.size} safe ATLAS declarations and all dependencies"
  M.run env do
    let _ ← initState env []
    dumpMetadata
    for name in roots do
      modify (fun st => { st with noMDataExprs := {} })
      dumpConstant name

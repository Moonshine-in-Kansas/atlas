import Atlas
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if n.isInternal || isPrivateName n then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.allImportedModuleNames[idx.toNat]!
    if !(mod.toString.startsWith "Atlas.") then continue
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .inductInfo _ => "inductive/structure"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
    logInfo m!"ATLAS_DECL\t{n}\t{mod}\t{kind}"

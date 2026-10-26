import Atlas
import Lean.Util.CollectAxioms
set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.allImportedModuleNames do logInfo m!"IMPORTED_MODULE {m}"
#print Atlas.Sporadic.Fischer22.Model
#print Atlas.Fischer.ResidueGroup
#print Atlas.Fischer.residueCentralizer
#print Atlas.Fischer.residueCentralElementary
#print Atlas.Fischer.fischer22Marking
#synth Group Atlas.Sporadic.Fischer22.Model
#synth Finite Atlas.Sporadic.Fischer22.Model
#check @Atlas.Sporadic.Fischer22.finite
#check @Atlas.Sporadic.Fischer22.card
#check @Atlas.Sporadic.Fischer22.simple
#check @Atlas.Sporadic.Fischer22.noncommutative
#print axioms Atlas.Sporadic.Fischer22.finite
#print axioms Atlas.Sporadic.Fischer22.card
#print axioms Atlas.Sporadic.Fischer22.simple
#print axioms Atlas.Sporadic.Fischer22.noncommutative
#print Atlas.Families.Cyclic.Model
#check @Atlas.Families.Cyclic.card
#check @Atlas.Families.Cyclic.isSimpleGroup
#check @Atlas.Families.Cyclic.commutative
#print axioms Atlas.Families.Cyclic.card
#print axioms Atlas.Families.Cyclic.isSimpleGroup
#print axioms Atlas.Families.Cyclic.commutative

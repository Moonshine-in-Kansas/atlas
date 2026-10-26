import Lake.Build.Trace

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw <| IO.userError "Expected a hash inventory"
  let mut checked := 0
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty then continue
    let columns := line.splitOn "\t"
    unless columns.length == 3 do
      throw <| IO.userError "Malformed cache inventory"
    let actual ← Lake.computeFileHash columns[1]! (columns[0]! == "text")
    unless actual.hex == columns[2]! do
      throw <| IO.userError s!"Stale cached input/output: {columns[1]!}; got {actual.hex}, expected {columns[2]!}"
    checked := checked + 1
  IO.println s!"PASS: {checked} Lake source/artifact hashes match the original build traces."

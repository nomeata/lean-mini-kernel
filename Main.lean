import MiniKernel.Parser
import MiniKernel.PP
import MiniKernel.Kernel

def runKernel (decls : Array Declaration) (liberal := false) : IO Unit := do
  let mut env : Environment := .empty
  let mut accepted := 0
  let mut rejeced := 0
  let mut skipped := 0
  for decl in decls do
    match env.add decl with
    | Except.error msg =>
      if liberal && msg.contains "Unknown constant" then
        skipped := skipped + 1
      else
        rejeced := rejeced + 1
        IO.println s!"Rejecting declaration {pp decl.name}:"
        IO.println s!"{msg}"
        unless liberal do
          IO.Process.exit 1
    | Except.ok newEnv =>
      env := newEnv
      accepted := accepted + 1
  IO.println s!"Accepted {accepted} declarations, rejected {rejeced} declarations with {skipped} depending declarations skipped."

def main (args : List String) : IO Unit := do
  let (flags, args) := args.partition (·.startsWith "--")
  let [inputPath] := args |
    throw <| .userError "Expected exactly one input file path as argument."
  let parseOnly := flags.contains "--parse-only"
  let liberal := flags.contains "--liberal"
  let handle ← IO.FS.Handle.mk inputPath .read
  let decls ←
    try
      Export.parseStream (.ofHandle handle) (liberal := liberal)
    catch e =>
      IO.println s!"Declinig to handle due to parse error:"
      IO.println s!"{e}"
      IO.Process.exit 2
  if parseOnly then
    IO.println s!"Successfully parsed {decls.size} declarations."
  else
    runKernel decls (liberal := liberal)

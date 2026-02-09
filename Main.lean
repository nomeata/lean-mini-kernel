import MiniKernel.Parser
import MiniKernel.PP
import MiniKernel.Kernel

def runKernel (decls : Array Declaration) : IO Unit := do
  let mut env : Environment := .empty
  for decl in decls do
    match env.add decl with
    | Except.error msg =>
      IO.println s!"Rejecting declaration {pp decl.name}:"
      IO.println s!"{msg}"
      IO.Process.exit 1
    | Except.ok newEnv =>
      env := newEnv
  IO.println s!"Accepted {decls.size} declarations."

def main (args : List String) : IO Unit := do
  let (inputPath, parseOnly) ← match args with
    | ["--parse-only", inputPath] => pure (inputPath, true)
    | [inputPath] => pure (inputPath, false)
    | _ => throw <| .userError "Expected input file path as first argument, optionally preceded by --parse-only."
  let handle ← IO.FS.Handle.mk inputPath .read
  let decls ←
    try
      Export.parseStream (.ofHandle handle)
    catch e =>
      IO.println s!"Declinig to handle due to parse error:"
      IO.println s!"{e}"
      IO.Process.exit 2
  if parseOnly then
    IO.println s!"Successfully parsed {decls.size} declarations."
  else
    runKernel decls

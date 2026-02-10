import MiniKernel.Types
import MiniKernel.ExprUtils

class PP (α : Type) where
  pp : α → String

export PP (pp)

def Name.pp : Name → String
  | .anonymous => "``_"
  | .str .anonymous s => s!"``{s}"
  | .str pre s => s!"{pre.pp}.{s}"
  | .num .anonymous i => s!"`{i}"
  | .num pre i => s!"{pre.pp}.{i}"

instance : PP Name where pp := Name.pp

def Level.toNat? : Level → Option Nat
  | .zero => some 0
  | .succ l => do
    let n ← l.toNat?
    some (n + 1)
  | _ => none

def Level.pp (level : Level) : String :=
  if let some n := level.toNat? then
    toString n
  else match level with
  | .zero => "0"
  | .succ l => s!"(succ {l.pp})"
  | .max l₁ l₂ => s!"(max {l₁.pp} {l₂.pp})"
  | .imax l₁ l₂ => s!"(imax {l₁.pp} {l₂.pp})"
  | .param n => n.pp

instance : PP Level where pp := Level.pp

partial def Expr.pp : Expr → String
  | .const name [] => name.pp
  | .const name levels =>
    let levelStr := String.intercalate ", " (levels.map Level.pp)
    name.pp ++ ".{" ++ levelStr ++ "}"
  | .bvar idx => s!"#{idx}"
  | .app f arg =>
    let fStr := match f with
      | .app _ _ => f.pp
      | _ => f.pp
    let argStr := match arg with
      | .app _ _ | .lam _ _ _ | .forall _ _ _ | .let _ _ _ _ => s!"({arg.pp})"
      | _ => arg.pp
    s!"{fStr} {argStr}"
  | .lam name type body => s!"fun {name.pp} : {type.pp} => {body.pp}"
  | .forall name type body =>
    let typeStr := match type with
      | .forall _ _ _ => s!"({type.pp})"
      | _ => type.pp
    if body.hasBVar 0 then
      let nStr := if name matches Name.str .anonymous _ then name.pp else "_"
      s!"∀ {nStr} : {typeStr}, {body.pp}"
    else
      s!"{typeStr} → {body.pp}"
  | .natLit n => toString n
  | .strLit s => s!"\"{s}\""
  | .sort level =>
    match level with
    | .zero => "Prop"
    | .succ .zero => "Type"
    | .succ l => s!"Type {l.pp}"
    | _ => s!"Sort {level.pp}"
  | .proj name idx e =>
    let eStr := match e with
      | .app _ _ | .lam _ _ _ | .forall _ _ _ | .let _ _ _ _ => s!"({e.pp})"
      | _ => e.pp
    s!"{eStr}.{name.pp}.{idx}"
  | .let name type value body => s!"let {name.pp} : {type.pp} := {value.pp} in {body.pp}"

instance : PP Expr where pp := Expr.pp

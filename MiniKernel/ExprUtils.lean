import MiniKernel.Types

def Name.simple (s : String) : Name := .str .anonymous s

def Level.isNotZero : Level → Bool
  | .zero => false
  | .max l1 l2 => isNotZero l1 || isNotZero l2
  | .imax _ l2 => isNotZero l2
  | .succ _ | .param _ => true

def Expr.hasBVar (idx : Nat): Expr → Bool
  | .bvar i => i == idx
  | .app f a => hasBVar idx f || hasBVar idx a
  | .lam _ type body => hasBVar idx type || hasBVar (idx + 1) body
  | .forall _ type body => hasBVar idx type || hasBVar (idx + 1) body
  | .let _ type value body => hasBVar idx type || hasBVar idx value || hasBVar (idx + 1) body
  | _ => false

def Expr.bvars (n : Nat) (d : Nat := 0) : Array Expr :=
  Array.range n |>.reverse |>.map (Expr.bvar <| · + d)

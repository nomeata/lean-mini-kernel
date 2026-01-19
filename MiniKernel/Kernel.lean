import MiniKernel.Types
import MiniKernel.PP

def Expr.shift (e : Expr) (n : Nat := 0) (d : Nat := 1) : Expr := match e with
  | .bvar idx => if idx >= n then .bvar (idx + d) else e
  | .app f a => .app (f.shift n d) (a.shift n d)
  | .lam name type body => .lam name (type.shift n d) (body.shift (n + 1) d)
  | .forall name type body => .forall name (type.shift n d) (body.shift (n + 1) d)
  | .let name type value body =>
    .let name (type.shift n d) (value.shift n d) (body.shift (n + 1) d)
  | .proj name idx e => .proj name idx (e.shift n d)
  | .const .. | .sort .. | .natLit .. | .strLit .. => e

def Expr.subst (e : Expr) (n : Nat := 0) (s : Expr) : Expr := match e with
  | Expr.bvar idx =>
    if idx = n then s
    else if idx > n then Expr.bvar (idx - 1)
    else e
  | .const name levels =>
    .const name levels
  | .app f a => .app (f.subst n s) (a.subst n s)
  | .lam name type body => .lam name (type.subst n s) (body.subst (n + 1) s.shift)
  | .forall name type body => .forall name (type.subst n s) (body.subst (n + 1) s.shift)
  | .let name type value body =>
    .let name (type.subst n s) (value.subst n s) (body.subst (n + 1) s.shift)
  | .proj name idx e => .proj name idx (e.subst n s)
  | .sort .. | .natLit .. | .strLit .. => e

structure LEnv where
  env : Environment
  /-- Valid level parameters -/
  lparams : Std.HashSet Name
  /-- Types of deBruijn indices -/
  lenv : List Expr := []

abbrev LEnvM := ReaderT LEnv (Except String)

def appendError {α} (msg : Unit → String) (action : LEnvM α) : LEnvM α := do
  match action.run (← read) with
  | .ok a => return a
  | .error e => throw (e ++ "\n" ++ msg ())

def Level.substLevel (l : Level) (f : Name → LEnvM Level) : LEnvM Level :=
  match l with
  | .param n => f n
  | .zero => return .zero
  | .succ l' => return .succ (← l'.substLevel f)
  | .max l1 l2 => return .max (← l1.substLevel f) (← l2.substLevel f)
  | .imax l1 l2 => return .imax (← l1.substLevel f) (← l2.substLevel f)

def Level.substOneLevel (l : Level) (n : Name) (l' : Level) : LEnvM Level :=
  l.substLevel fun m => if m == n then return l' else return .param m

def Expr.substLevel (e : Expr) (f : Name → LEnvM Level) : LEnvM Expr := match e with
  | .const name levels => return .const name (← levels.mapM (·.substLevel f))
  | .app fn a => return .app (← fn.substLevel f) (← a.substLevel f)
  | .lam name type body =>
    return .lam name (← type.substLevel f) (← body.substLevel f)
  | .forall name type body =>
    return .forall name (← type.substLevel f) (← body.substLevel f)
  | .let name type value body =>
    return .let name (← type.substLevel f) (← value.substLevel f) (← body.substLevel f)
  | .proj name idx e =>
    return .proj name idx (← e.substLevel f)
  | .sort l => return .sort (← l.substLevel f)
  | .bvar .. | .natLit .. | .strLit .. => return e

def sort (e : Expr) : LEnvM Level :=
  match e with
  | .sort u => return u
  | _ => throw "Expected a sort"

def assertIsSort (e : Expr) : LEnvM Unit := discard <| sort e

def openType (type : Expr) : LEnvM α → LEnvM α :=
  withReader (fun lenv => { lenv with lenv := type :: lenv.lenv })

def ConstantInfo.type (cinfo : ConstantInfo) : Expr :=
  match cinfo with
  | .axiom _ type => type
  | .def _ type _ _ => type
  | .special _ type => type

def ConstantInfo.lparams (cinfo : ConstantInfo) : List Name  :=
  match cinfo with
  | .axiom lparams _ => lparams
  | .def lparams _ _ _ => lparams
  | .special lparams _ => lparams

def ConstantInfo.value? (cinfo : ConstantInfo) : Option Expr :=
  match cinfo with
  | .axiom _ _ => none
  | .def _ _ value _ => some value
  | .special _ _ => none

@[extern "assertIsDefEq"]
opaque assertIsDefEq (e1 e2 : Expr) : LEnvM Unit

def Expr.instantiateLParams (e : Expr) (lparams : List Name) (levels : List Level) : LEnvM Expr := do
  unless levels.length = lparams.length do
    throw s!"Expected {lparams.length} levels, got {levels.length}"
  e.substLevel fun n =>
    match lparams.idxOf? n with
    | some idx => return levels[idx]!
    | none => throw s!"Level parameter {PP.pp n} not found"

partial def whnf : Expr → LEnvM Expr
  | e@(.const name levels) => do
    let some cinfo := (← read).env.consts[name]?  | throw s!"Unknown constant {pp name}"
    let some value := cinfo.value?  | return e
    let value ← value.instantiateLParams cinfo.lparams levels
    whnf value
  | .app f a => do
    let f' ← whnf f
    match f' with
    | .lam _ _ body => whnf (body.subst 0 a)
    | _ =>
      return .app f' a
  | e => return e  -- Very naive implementation: no reduction

partial def inferType : Expr → LEnvM Expr
  | .bvar idx => do
    let some t := (← read).lenv[idx]?
      |  throw s!"deBruijn index #{idx} out of bounds"
    return t.shift (d := idx + 1)
  | .const name levels => do
    let some cinfo := (← read).env.consts[name]?
      | throw s!"Unknown constant {pp name}"
    let type := cinfo.type
    let type ← type.instantiateLParams cinfo.lparams levels
    pure type
  | .sort u => do
    return .sort u.succ
  | .app f arg => do
    let fType ← inferType f
    let fType ← whnf fType
    match fType with
    | .forall _ type body => do
      let argType ← inferType arg
      assertIsDefEq type argType
      return body.subst 0 arg
    | _ => throw s!"Expected a function type in application of {pp f} to {pp arg}, got {pp fType}"
  | .forall _ type body => do
    let s1 ← inferType type
    let l1 ← sort s1
    let s2 ← openType type <| inferType body
    let l2 ← sort s2
    let u := Level.imax l1 l2
    return .sort u
  | .lam name type body => do
    let s1 ← inferType type
    assertIsSort s1
    let t2 ← openType type <| inferType body
    return .forall name type t2
  | e => throw <| "Type inference not yet implemented:\n" ++ pp e

/--
Smart constructor that ensures the invariant that the rhs of `imax` is always a parameter.
-/
def Level.mkIMax (l1 l2 : Level) : Level :=
  match l2 with
  | .zero =>        .zero
  | .succ _ =>      .max l1 l2
  | .max l21 l22 => .max (l1.mkIMax l21) (l1.mkIMax l22)
  | .imax l21 l22 =>.mkIMax (l1.max l21) l22
  | .param _  =>    .imax l1 l2

/--
Simplification ensures the invariant that the rhs of an `imax` is always a parameter.
-/
partial def Level.simplify : Level → Level
  | .zero => .zero
  | .succ l => .succ (l.simplify)
  | .max l1 l2 => .max (l1.simplify) (l2.simplify)
  | .imax l1 l2 => .mkIMax (l1.simplify) (l2.simplify)
  | .param n => .param n

-- Implementation inspired by https://ammkrn.github.io/type_checking_in_lean4/levels.html
-- TOODO: Params
mutual
partial def Level.le (l1 l2 : Level) (balance : Int := 0) : LEnvM Bool :=
  match l1, l2 with
  | .succ l1', l2 => Level.le l1' l2 (balance - 1)
  | l1, .succ l2' => Level.le l1 l2' (balance + 1)
  | .max l1a l1b, l2 =>
    Level.le l1a l2 balance <&&> Level.le l1b l2 balance
  | l1, .max l2a l2b =>
    Level.le l1 l2a balance <||> Level.le l1 l2b balance
  | .zero, .zero => if balance >= 0 then return true else return false
  | .param n, .param m => return n == m && balance >= 0
  | .imax _ (.param p), _ | _, .imax _ (.param p) =>
    cases p l1 l2
  | l1, l2 => throw s!"Level.le not implemented for {pp l1} ≤ {pp l2}"

partial def cases (p : Name) (l1 l2 : Level) : LEnvM Bool := do
  (← l1.substOneLevel p Level.zero).simplify.le (← l2.substOneLevel p Level.zero).simplify
    <&&>
  (← l1.substOneLevel p (Level.param p).succ).simplify.le (← l2.substOneLevel p (Level.param p).succ).simplify
end

def assertLevelLe (l1 l2 : Level) : LEnvM Unit :=
  unless (← l1.simplify.le l2.simplify) do
    throw s!"Expected level inequality does not hold: {pp l1} ≤ {pp l2}"

def assertLevelEq (l1 l2 : Level) : LEnvM Unit :=
  unless (← l1.simplify.le l2.simplify) && (← l2.simplify.le l1.simplify) do
    throw s!"Expected level equality does not hold: {pp l1} = {pp l2}"

@[export assertIsDefEq]
partial def assertIsDefEqImpl (e1 e2 : Expr) : LEnvM Unit := do
  appendError (fun _ => s!"… while checking {pp e1} =?= {pp e2}") do
  let e1 ← whnf e1
  let e2 ← whnf e2
  match e1, e2 with
  | .sort l1, .sort l2 =>
    assertLevelEq l1 l2
  | .forall _ t1 b1, .forall _ t2 b2 =>
    assertIsDefEq t1 t2
    openType t1 <| assertIsDefEq b1 b2
  | .lam _ t1 b1, .lam _ t2 b2 =>
    assertIsDefEq t1 t2
    openType t1 <| assertIsDefEq b1 b2
  | .bvar n1, .bvar n2 =>
    unless n1 == n2 do
      throw s!"Expected definitional equality between {pp e1} and {pp e2}, but they differ."
  | .app f1 a1, .app f2 a2 =>
    assertIsDefEq f1 f2
    assertIsDefEq a1 a2
  | e1, e2 =>
    throw s!"Expected definitional equality between {pp e1} and {pp e2}, but they differ."


def Environment.add (env : Environment) (decl : Declaration) : Except String Environment :=
  match decl with
  | .axiom name lparams type =>
    return { env with consts := env.consts.insert name (.axiom lparams type) }
  | .def name lparams type value isUnsafe => do
    unless lparams.Nodup do
      throw s!"Duplicate level parameters in declaration of {pp name}"
    ReaderT.run (r := { env, lparams := .ofList lparams}) do
      let s ← inferType type
      assertIsSort s
      let type' ← inferType value
      assertIsDefEq type type'
      pure ()
    return { env with consts := env.consts.insert name (.def lparams type value isUnsafe) }
  | .quot =>
    -- throw "Quotients not yet supported"
    pure env

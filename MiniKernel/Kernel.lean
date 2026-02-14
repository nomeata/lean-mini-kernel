import MiniKernel.Types
import MiniKernel.PP

def Expr.getApp : Expr → Expr × Array Expr
  | .app f a => let (f, xs) := f.getApp; (f, xs.push a)
  | e => (e, #[])

def Expr.appN (f : Expr) (args : Array Expr) : Expr :=
  args.foldl .app f

def Expr.shift (e : Expr) (n : Nat := 0) (d : Nat := 1) : Expr := match e with
  | .bvar idx => if idx >= n then .bvar (idx + d) else e
  | .app f a => .app (f.shift n d) (a.shift n d)
  | .lam name type body => .lam name (type.shift n d) (body.shift (n + 1) d)
  | .forall name type body => .forall name (type.shift n d) (body.shift (n + 1) d)
  | .let name type value body =>
    .let name (type.shift n d) (value.shift n d) (body.shift (n + 1) d)
  | .proj name idx e => .proj name idx (e.shift n d)
  | .const .. | .sort .. | .natLit .. | .strLit .. => e

def Expr.substs (e : Expr) (s : Array Expr) (n : Nat := 0) : Expr := match e with
  | Expr.bvar idx =>
    if _ : idx >= n then
      if _ : idx < n + s.size then
        let s := s[s.size - (idx - n + 1)]
        s.shift (d := n)
      else
        .bvar (idx - s.size)
    else
      e
  | .const name levels =>
    .const name levels
  | .app f a => .app (f.substs s n) (a.substs s n)
  | .lam name type body => .lam name (type.substs s n) (body.substs s (n := n + 1))
  | .forall name type body => .forall name (type.substs s n) (body.substs  s (n := n + 1))
  | .let name type value body =>
    .let name (type.substs s n) (value.substs s n) (body.substs s (n := n + 1))
  | .proj name idx e => .proj name idx (e.substs s n)
  | .sort .. | .natLit .. | .strLit .. => e

def Expr.subst (e : Expr) (a : Expr) : Expr := e.substs #[a]

structure LEnv where
  env : Environment
  /-- Valid level parameters -/
  lparams : Std.HashSet Name
  /--
  Local typing environment, as a telescope.

  The type of `.bvar` is `lenv[i]`, where a `.bvar j` in that type has
  type `lenv[i + j + 1]`.
  -/
  lenv : List Expr := []

abbrev LEnvM := ReaderT LEnv (Except String)

def appendError {α} (msg : Unit → String) (action : LEnvM α) : LEnvM α := do
  match action.run (← read) with
  | .ok a => return a
  | .error e => throw (e ++ "\n" ++ msg ())

def Level.substLevel (l : Level) (f : Name → Level) : Level :=
  match l with
  | .param n => f n
  | .zero => .zero
  | .succ l' => .succ (l'.substLevel f)
  | .max l1 l2 => .max (l1.substLevel f) (l2.substLevel f)
  | .imax l1 l2 => .imax (l1.substLevel f) (l2.substLevel f)

def Level.substOneLevel (l : Level) (n : Name) (l' : Level) : Level :=
  l.substLevel fun m => if m == n then l' else .param m

def Expr.substLevel (e : Expr) (f : Name → Level) : Expr := match e with
  | .const name levels => .const name (levels.map (·.substLevel f))
  | .app fn a => .app (fn.substLevel f) (a.substLevel f)
  | .lam name type body =>
    .lam name (type.substLevel f) (body.substLevel f)
  | .forall name type body =>
    .forall name (type.substLevel f) (body.substLevel f)
  | .let name type value body =>
    .let name (type.substLevel f) (value.substLevel f) (body.substLevel f)
  | .proj name idx e =>
    .proj name idx (e.substLevel f)
  | .sort l => .sort (l.substLevel f)
  | .bvar .. | .natLit .. | .strLit .. => e

def sort (e : Expr) : LEnvM Level :=
  match e with
  | .sort u => return u
  | _ => throw s!"Expected a sort, got {pp e}"

def assertIsSort (e : Expr) : LEnvM Unit := discard <| sort e

def openType (type : Expr) : LEnvM α → LEnvM α :=
  withReader (fun lenv => { lenv with lenv := type :: lenv.lenv })

/-- Adds the (non-dependent) types to the local context -/
def openTypes (types : Array Expr) : LEnvM α → LEnvM α :=
  let types := types.mapIdx fun i type => type.shift (d := i)
  withReader (fun lenv => { lenv with lenv := types.reverse.toList ++ lenv.lenv })

def readLocalTypes (n : Nat) : LEnvM (Array Expr) := do
  let lenv := (← read).lenv
  if lenv.length < n then
    throw s!"Expected at least {n} local variables, got {lenv.length}"
  return lenv.take n |>.mapIdx (fun i t => t.shift (d := i + 1)) |>.reverse |>.toArray

def ConstantInfo.lparams (cinfo : ConstantInfo) : List Name  :=
  match cinfo with
  | .opaque lparams _ => lparams
  | .inductive lparams .. => lparams
  | .def lparams _ _ => lparams
  | .recursor lparams _ _ _ _ _ => lparams
  | .special lparams _ => lparams

def ConstantInfo.type (cinfo : ConstantInfo) : Expr :=
  match cinfo with
  | .opaque _ type => type
  | .inductive _ type .. => type
  | .def _ type _ => type
  | .recursor _ type _ _ _ _ => type
  | .special _ type => type

def ConstantInfo.value? (cinfo : ConstantInfo) : Option Expr :=
  match cinfo with
  | .def _ _ value => some value
  | _ => none

@[extern "assertIsDefEq"]
opaque assertIsDefEq (e1 e2 : Expr) : LEnvM Unit

def Expr.instantiateLParams (e : Expr) (lparams : List Name) (levels : List Level) : LEnvM Expr := do
  unless levels.length = lparams.length do
    throw s!"Expected {lparams.length} levels, got {levels.length}"
  return e.substLevel fun n =>
    match lparams.idxOf? n with
    | some idx => levels[idx]!
    | none => .param n -- should not happen

partial def whnf (e : Expr) : LEnvM Expr :=
  go e []
where
  go : Expr → List Expr → LEnvM Expr
  | e@(.const name levels), stack => do
    let some cinfo := (← read).env.consts[name]?  | throw s!"Unknown constant {pp name}"
    if let some value := cinfo.value? then
      let value ← value.instantiateLParams cinfo.lparams levels
      return ← go value stack
    if let .recursor _ _ numParams numMinors numIndices rules := cinfo then
      let majorPos := numParams + 1 + numMinors + numIndices
      if let some major := stack[majorPos]? then
        let major' ← whnf major
        if let (.const f _, conArgs) := major.getApp then
          if let some (_, rhs) := rules.find? (fun (ctorName, _) => ctorName == f) then
            let fields := conArgs[numParams:]
            let args := stack.toArray[:numParams + 1 + numMinors] ++ fields |>.toArray
            let rhs ← rhs.instantiateLParams cinfo.lparams levels
            let rhs := rhs.substs args
            return ← go rhs (stack.drop (majorPos + 1))
        let stack' := stack.set majorPos major'
        return e.appN stack'.toArray
    return e.appN stack.toArray
  | .app f a, stack => do
    go f (a :: stack)
  | .lam _ _ body, a::stack =>
    go (body.subst a) stack
  | e, stack =>
    return e.appN stack.toArray  -- Very naive implementation: no reduction

def getLocalType (idx : Nat) : LEnvM Expr := do
  let some t := (← read).lenv[idx]?
    |  throw s!"deBruijn index #{idx} out of bounds"
  return t.shift (d := idx + 1)

mutual
partial def inferType : Expr → LEnvM Expr
  | .bvar idx => do
    getLocalType idx
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
      return body.subst arg
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
  | .let _name type value body => do
    let s1 ← inferType type
    assertIsSort s1
    let valueType ← inferType value
    assertIsDefEq type valueType
    let body' := body.subst value
    inferType body'
  | .proj n idx e => inferProj n idx e
  | e => throw <| "Type inference not yet implemented:\n" ++ pp e

partial def isProp (type : Expr) : LEnvM Bool := do
  let s ← inferType type
  let u ← sort s
  return u.isZero

partial def inferProj (n : Name) (idx : Nat) (e : Expr) : LEnvM Expr := do
  let type ← whnf (← inferType e)
  let (.const indName us, args) := type.getApp
    | throw s!"Type of projected expression is not an inductive: {pp type}"
  let some (.inductive _lparams _indType numParams numIndices ctors)
      := (← read).env.consts[indName]?
    | throw s!"Type of projected expression is not an inductive: {pp type}"
  -- Unclear if this can be happen, if `e` is well-typed:
  unless args.size = numParams + numIndices do
    throw s!"Invalid projection, expression is not fully applied"
  let #[ctorName] := ctors
    | throw s!"Invalid projection, {pp indName} has not exactly one constructor"
  -- The validity of a projection depends on the type that the single
  -- constructor would have here, given the concrete level and expression parameters
  let some (.opaque ctorlparams ctorType) := (← read).env.consts[ctorName]?
    | throw s!"Constructor {pp ctorName} not found in environment"
  let ctorType ← ctorType.instantiateLParams ctorlparams us
  let mut ctorType ← instantiateForalls ctorType args[:numParams]
  let isPropType ← isProp ctorType
  for i in [:idx] do
    let .forall _ d b := ctorType
      | throw s!"Projection index {idx+1} out of bounds for {pp indName}"
    if isPropType && b.hasBVar 0 then
      unless (← isProp d) do
        throw s!"Invalid projection; projection {i+1} is depended upon and not a proposition."
    ctorType := b.subst (.proj n i e)
  let .forall _ d _b := ctorType
    | throw s!"Projection index {idx+1} out of bounds for {pp indName}"
  if isPropType then
    unless (← isProp d) do
      throw s!"Invalid projection; projection {idx+1} would project data out of a proposition"
  return d

partial def openForall (n : Nat) (type : Expr) (k : Expr → LEnvM α) : LEnvM α := do
  match n with
  | 0 => k type
  | n+1 =>
    let type' ← whnf type
    let .forall _ domain body := type' | throw s!"Insufficient number of parameters: {pp type}"
    openType domain do
      openForall n body k

partial def instantiateForalls (type : Expr) (xs : Array Expr) : LEnvM Expr := do
  let mut result := type
  for x in xs do
    let type' ← whnf result
    let .forall _ _ body := type' | throw s!"Expected a function type, got {pp type'}"
    result := body.subst x
  return result

partial def openForallEager (type : Expr) (k : Nat → Expr → LEnvM α) : LEnvM α := do
  let type' ← whnf type
  if let .forall _ domain body := type' then
    openType domain do
        openForallEager body fun n r => k (n + 1) r
  else
    k 0 type

/-- Wrapps `types` in `n` foralls, with types taken from the local environment -/
partial def mkForall (n : Nat) (body : Expr) : LEnvM Expr := do
  let types := (← read).lenv.take n
  return types.foldl (fun body type => .forall .anonymous type body) body
end

def checkType (e : Expr) : LEnvM Unit := do
  let _ ← inferType e

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
def Level.simplify : Level → Level
  | .zero => .zero
  | .succ l => .succ l.simplify
  | .max l1 l2 => .max l1.simplify l2.simplify
  | .imax l1 l2 => .mkIMax l1.simplify l2.simplify
  | .param n => .param n

def Level.byCases (p : Name) (l1 l2 : Level) (k : (l1 l2 : Level) → Bool) : Bool :=
  k (l1.substOneLevel p Level.zero).simplify (l2.substOneLevel p Level.zero).simplify &&
  k (l1.substOneLevel p (Level.param p).succ).simplify (l2.substOneLevel p (Level.param p).succ).simplify

-- Implementation inspired by https://ammkrn.github.io/type_checking_in_lean4/levels.html
partial def Level.le (l1 l2 : Level) (balance : Int := 0) : Bool :=
  match _ : l1, _ : l2, decide (0 ≤ balance) with
  | .succ l1', l2, _ => Level.le l1' l2 (balance - 1)
  | l1, .succ l2', _ => Level.le l1 l2' (balance + 1)
  | .max l1a l1b, l2, _ =>
    Level.le l1a l2 balance && Level.le l1b l2 balance
  | .param n, .param m, _ => n == m && balance >= 0
  | .imax _ (.param p), _, _ | _, .imax _ (.param p), _ =>
    Level.byCases p l1 l2 (fun l1' l2' => Level.le l1' l2' balance)
  | .imax _ _, _, _ | _, .imax _ _, _  => false -- unreachable by the simplification invariant
  | param _, .max l2a l2b, _ | zero, .max l2a l2b, _  =>
    Level.le l1 l2a balance || Level.le l1 l2b balance
  | .zero, _, true => true
  | .zero, .param _, false => false
  | _, .zero, false => false
  | .param _, .zero, _ => false

def assertLevelLe (l1 l2 : Level) : LEnvM Unit :=
  unless (l1.simplify.le l2.simplify) do
    throw s!"Expected level inequality does not hold: {pp l1} ≤ {pp l2}"

def assertLevelEq (l1 l2 : Level) : LEnvM Unit :=
  unless (l1.simplify.le l2.simplify) && (l2.simplify.le l1.simplify) do
    throw s!"Expected level equality does not hold: {pp l1} = {pp l2}"

@[export assertIsDefEq]
partial def assertIsDefEqImpl (e1 e2 : Expr) : LEnvM Unit := do
  appendError (fun _ => s!"… while checking {pp e1} =?= {pp e2}") do
  let e1 ← whnf e1
  let e2 ← whnf e2
  appendError (fun _ => s!"… while checking {pp e1} =?= {pp e2}") do
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
  | .const n1 ls1, .const n2 ls2 =>
    unless n1 == n2 do
      throw s!"Expected definitional equality between {pp e1} and {pp e2}, but they differ."
    unless ls1.length == ls2.length do
      throw s!"Mismatched level parameter list when checking {pp e1} =?= {pp e2}"
    appendError (fun _ => s!"… while checking level parameters of {pp e1} =?= {pp e2}") do
      for (l1, l2) in List.zip ls1 ls2 do
        assertLevelEq l1 l2
  | .proj n1 idx1 e1, .proj n2 idx2 e2 =>
    unless n1 == n2 && idx1 == idx2 do
      throw s!"Projections differ: {pp e1} =?= {pp e2}"
    assertIsDefEq e1 e2
  | e1, e2 =>
    throw s!"Expected definitional equality between {pp e1} and {pp e2}, but they differ."

partial def freshLevelName (used : List Name) : Name :=
  let rec loop (n : Nat) : Name :=
    let name := if n = 0 then .simple "v" else .simple s!"v{n}"
    if used.contains name then loop (n + 1) else name
  loop 0

def hasConst (n : Name) : Expr → Bool
  | .const name _ => name == n
  | .app f a => hasConst n f || hasConst n a
  | .lam _ type body => hasConst n type || hasConst n body
  | .forall _ type body => hasConst n type || hasConst n body
  | .let _ type value body => hasConst n type || hasConst n value || hasConst n body
  | .proj _ _ e => hasConst n e
  | .bvar .. | .sort .. | .natLit .. | .strLit .. => false

/- Are the parameters defeq -/
partial def defEqParams (n : Nat) (type1 type2 : Expr) : LEnvM Unit := do
  match n with
  | 0 => pure ()
  | n+1 =>
    -- We do not whnf here (the official kernel does not whnf either)
    let .forall _ domain1 body1 := type1 | throw s!"Expected a function type, got {pp type1}"
    let .forall _ domain2 body2 := type2 | throw s!"Expected a function type, got {pp type2}"
    assertIsDefEq domain1 domain2
    openType domain1 do
      defEqParams n body1 body2

partial def Environment.add (env : Environment) (decl : Declaration) : Except String Environment :=
  match decl with
  | .axiom name lparams type =>do
    unless lparams.Nodup do
      throw s!"Duplicate level parameters in declaration of {pp name}"
    ReaderT.run (r := { env, lparams := .ofList lparams}) do
      let _ ← inferType type
    -- TODO: Check for duplicate names
    return { env with consts := env.consts.insert name (.opaque lparams type) }
  | .def name lparams type value kind => do
    unless lparams.Nodup do
      throw s!"Duplicate level parameters in declaration of {pp name}"
    ReaderT.run (r := { env, lparams := .ofList lparams}) do
      let s ← inferType type
      assertIsSort s
      let type' ← inferType value
      assertIsDefEq type type'
      pure ()
    -- TODO: Check for duplicate names
    let constInfo  ← match kind with
      | .«def» | .«theorem» => pure <| .def lparams type value
      | .«opaque» => pure <| .opaque lparams type
    return { env with consts := env.consts.insert name constInfo }
  | .quot =>
    -- throw "Quotients not yet supported"
    pure env
  | .inductive indName lparams numParams indType ctors => do
    let mut env := env
    unless lparams.Nodup do
      throw s!"Duplicate level parameters in declaration of {pp indName}"
    let numCtors := ctors.size
    let (numIndices, indLevel) ←
      ReaderT.run (r := { env, lparams := .ofList lparams}) do
        appendError (fun _ => s!"… while checking type of inductive {pp indName}") do
          checkType indType
          openForall numParams indType fun indType =>
            openForallEager indType fun numIndices indType => do
              let u ← sort indType
              return (numIndices, u)

    let indInfo := .inductive lparams indType numParams numIndices (ctors.map (·.1))
    env := { env with consts := env.consts.insert indName indInfo }
    ReaderT.run (r := { env, lparams := .ofList lparams}) do
      for (ctorName, ctorType) in ctors do
        appendError (fun _ => s!"… while checking type of constructor {pp ctorName}") do
          checkType ctorType
        appendError (fun _ => s!"… while checking parameters of constructor {pp ctorName} match those of {pp indName}") do
          defEqParams numParams indType ctorType

        let isValidIndApp (shift : Nat) (type : Expr) : LEnvM Unit := do
          let (.const f us, args) := type.getApp |
            throw s!"Expected an application headed by the current inductive, got {pp type}"
          unless f == indName do
            throw s!"Expected an application headed by the current inductive, got {pp type}"
          unless us == lparams.map (.param) do
            throw s!"Level parameters do not match those of {pp indName} in {pp type}"
          unless args.size = numParams + numIndices do
            throw s!"Expected {numParams + numIndices} arguments, got {args.size} in {pp type}"
          for i in [:numParams] do
            unless args[i]! == .bvar (shift + numParams - (i+1)) do
              throw s!"Unexpected parameter {i+1} in {pp type}"
          for i in [numParams:args.size] do
            if hasConst indName args[i]! then
              throw s!"Unexpected recursive occurrence of {pp indName} in index argument {i+1} of {pp type}"

        let rec checkCtorParam shift argIdx ctorParam := do
          appendError (fun _ => s!"… while checking argument {argIdx} of {pp ctorName}") do
            let s ← inferType ctorParam
            let u ← sort s
            unless indLevel matches .zero do
              assertLevelLe u indLevel
            let ctorParam ← whnf ctorParam
            if (hasConst indName ctorParam) then
              -- TODO: Reflexive occurrences
              isValidIndApp shift ctorParam


        let rec checkCtorType shift argIdx ctorType := do
          -- NB: We do **not** whnf here (the official kernel does not)
          if let .forall _ domain body := ctorType then
            checkCtorParam shift argIdx domain
            openType domain do
              checkCtorType (shift + 1) (argIdx + 1) body
          else
            appendError (fun _ => s!"… while checking return type of {pp ctorName}") do
              isValidIndApp shift ctorType

        openForall numParams ctorType fun ctorType => do
          checkCtorType 0 (numParams + 1) ctorType

    for (ctorName, ctorType) in ctors do
      env := { env with consts := env.consts.insert ctorName (.opaque lparams ctorType) }

    -- Now we can generate the recursors
    let elimToSort ← ReaderT.run (r := { env, lparams := .ofList lparams}) do
      if indLevel.isNotZero then
        return true
      -- TODO: mutual inductives should return false
      if numCtors = 0 then
        return true
      if numCtors > 1 then
        return false
      let (_, ctorType) := ctors[0]!

      let rec go (t : Expr) : LEnvM Bool := do
        match t with
        | .forall _ domain body =>
          let s ← inferType domain
          let u ← sort s
          openType domain do
            let appearsInType ← openForallEager body fun shift resType =>
                return resType.getApp.2.contains (.bvar shift)
            unless u matches .zero || appearsInType do
              return false
            go body
        | _ => return true
      go ctorType


    let (motiveLevel, lparams') ← if elimToSort then
      let v := freshLevelName lparams
      pure (.param v, v::lparams)
    else
      pure (.zero, lparams)
    let us := lparams.map .param
    let us' := lparams'.map .param
    let recType ← ReaderT.run (r := { env, lparams := .ofList lparams'}) do
      -- 1. Parameters
      let recType ← openForall numParams indType fun indType => do
        -- 2. Motive
        let motiveType ← openForall numIndices indType fun _majorType => do
          let params := Expr.bvars numParams numIndices
          let idxs := Expr.bvars numIndices
          let majorType := (Expr.const indName us).appN (params ++ idxs)
          openType majorType do
            mkForall (numIndices + 1) (.sort motiveLevel)
        openType motiveType do
          -- 3. Minors
          let minorTypes ← ctors.mapM fun (ctorName, ctorType) => do
            let params := Expr.bvars numParams 1
            let ctorType ← instantiateForalls ctorType params
            openForallEager ctorType fun numFields ctorResType => do
              -- Look at the type of the fields, find recursive ones, and
              -- calculate the inductive hypothesis from these
              let hypTypes ← (Expr.bvars numFields).filterMapM fun field => do
                let t ← inferType field
                let t ← whnf t
                if hasConst indName t then
                  -- TODO: reflexive occurrences
                  let idxs := t.getApp.2[numParams:numParams+numIndices]
                  let motive := Expr.bvar numFields
                  let hypType := motive.appN (idxs ++ #[field])
                  pure (some hypType)
                else
                  pure none
              openTypes hypTypes do
                let ctorResType := ctorResType.shift (d := hypTypes.size)
                let params := params.map (·.shift (d := numFields + hypTypes.size))
                let fields := Expr.bvars numFields hypTypes.size
                let ctorApp := (Expr.const ctorName us).appN (params ++ fields)
                let idxs := ctorResType.getApp.2[numParams:numParams+numIndices]
                let motive := Expr.bvar (numFields + hypTypes.size)
                let motiveApp := motive.appN (idxs ++ #[ctorApp])
                mkForall (numFields + hypTypes.size) motiveApp
          openTypes minorTypes do
            -- 4. Indices
            openForall numIndices (indType.shift (d := 1 + numCtors)) fun _ => do
              -- 5. Major argument
              let params := Expr.bvars numParams (1 + numCtors + numIndices)
              let idxs := Expr.bvars numIndices
              let majorType := (Expr.const indName us).appN (params ++ idxs)
              openType majorType do
                -- 6. Result type: motive applied to indices and major argument
                let motive : Expr := .bvar (numCtors + numIndices + 1)
                let idxs := Expr.bvars numIndices 1
                let major := .bvar 0
                let resultType := motive.appN (idxs ++ #[major])
                mkForall (numParams + 1 + numCtors + numIndices + 1) resultType
      -- Sanity check:
      appendError (fun _ => s!"… while checking type of recursor for {pp indName}:\n{pp recType}") do
        checkType recType
      pure recType

    let recName := indName.str "rec"
    let rules ← ctors.mapIdxM fun i (ctorName, ctorType) => do
      ReaderT.run (r := { env, lparams := .ofList lparams'}) do
        openForall (numParams + 1 + numCtors) recType fun _recType => do
          let ctorType ← instantiateForalls ctorType (Expr.bvars numParams (1 + numCtors))
          openForallEager ctorType fun numFields _ => do
            let minor  := Expr.bvar (numCtors - (i + 1) + numFields)
            let fields := Expr.bvars numFields
            let ihs ← fields.filterMapM fun field => do
              let t ← inferType field
              let t ← whnf t
              if hasConst indName t then
                -- TODO: reflexive occurrences
                let idxs := t.getApp.2[numParams:numParams+numIndices]
                let recApp := Expr.const recName us'
                let ih := recApp.appN (Expr.bvars (numParams + 1 + numCtors) numFields ++ idxs ++ #[field])
                pure (some ih)
              else
                pure none
            let rhs := minor.appN (fields ++ ihs)
            return (ctorName, rhs)

    let recInfo := ConstantInfo.recursor lparams' recType numParams numCtors numIndices rules
    env := { env with consts := env.consts.insert recName recInfo }

    pure env

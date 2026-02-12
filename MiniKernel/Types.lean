import Std

inductive Name where
  | anonymous : Name
  | str (pre : Name) (str : String)
  | num (pre : Name) (i : Nat)
deriving BEq, ReflBEq, LawfulBEq, Hashable, DecidableEq, Inhabited

inductive Level
  | zero : Level
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  | param : Name → Level
deriving Inhabited, BEq

inductive Expr
  | const : Name → List Level → Expr
  | bvar : Nat → Expr
  | app : Expr → Expr → Expr
  | lam : Name → (type body : Expr) → Expr
  | forall : Name → (type body : Expr) → Expr
  | natLit : Nat → Expr
  | strLit : String → Expr
  | sort : Level → Expr
  | proj : Name → (idx : Nat) → (e : Expr) → Expr
  | let : Name → (type value body : Expr) → Expr
deriving Inhabited, BEq

inductive DefKind where
  | «def»
  | «theorem»
  | «opaque»

/--
A Declaration is something that can be sent to the kernel.
-/
inductive Declaration where
  | «axiom» : (name : Name) → (levelParams : List Name) → (type : Expr) → Declaration
  | «def» : (name : Name) → (levelParams : List Name) → (type : Expr) → (value : Expr) → (kind : DefKind) → Declaration
  | «quot» : Declaration
  | «inductive» : (name : Name) → (levelParams : List Name) → (numParams : Nat) → (type : Expr) → (ctors : Array (Name × Expr)) → Declaration

def Declaration.name : Declaration → Name
  | .axiom name _ _ => name
  | .def name _ _ _ _ => name
  | .quot => Name.anonymous.str "Quot"
  | .inductive name .. => name

/--
A ConstantInfo is what the kernel stores in the environment.
-/
inductive ConstantInfo
  /-- Any kind of inert opaque definition (axiom, opaque, inductive, constructor) -/
  | «opaque» : (levelParams : List Name) → (type : Expr) → ConstantInfo
  /-- Any kind of transparent definition (def, theorem) -/
  | «def» : (levelParams : List Name) → (type : Expr) → (value : Expr) → ConstantInfo
  /--
  A recursors. The rules list the supported constructors, and the RHS
  is an open expression that's the body of a lambda
  `fun params motive minors fields => …`.
  -/
  | «recursor» : (levelParams : List Name) → (type : Expr) →
    (numParams numMinors numIndices : Nat) →
    (rules : Array (Name × Expr)) →
    ConstantInfo
  /-- Used for quotients (maybe) -/
  | special : (levelParams : List Name) → (type : Expr) → ConstantInfo

structure Environment where
  consts : Std.HashMap Name ConstantInfo := {}

def Environment.empty : Environment := {}

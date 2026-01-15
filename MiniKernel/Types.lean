import Std

inductive Name where
  | anonymous : Name
  | str (pre : Name) (str : String)
  | num (pre : Name) (i : Nat)
deriving BEq, Hashable

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
deriving BEq

inductive DefKind where
  | «def»
  | «theorem»
  | «opaque»
  | «quot»

/--
A Declaration is something that can be sent to the kernel.
-/
inductive Declaration where
  | «axiom» : (name : Name) → (levelParams : List Name) → (type : Expr) → Declaration
  | «def» : (name : Name) → (levelParams : List Name) → (type : Expr) → (value : Expr) → (kind : DefKind) → Declaration
  | «quot» : Declaration

def Declaration.name : Declaration → Name
  | .axiom name _ _ => name
  | .def name _ _ _ _ => name
  | .quot => Name.anonymous.str "Quot"

/--
A ConstantInfo is what the kernel stores in the environment.
-/
inductive ConstantInfo
  | «axiom» : (levelParams : List Name) → (type : Expr) → ConstantInfo
  | «def» : (levelParams : List Name) → (type : Expr) → (value : Expr) → (kind : DefKind) → ConstantInfo
  /-- Used for the quotients and recursors -/
  | special : (levelParams : List Name) → (type : Expr) → ConstantInfo

structure Environment where
  consts : Std.HashMap Name ConstantInfo := {}

def Environment.empty : Environment := {}

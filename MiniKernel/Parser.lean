/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Joachim Breitner
-/
import Std
import Std.Internal.Parsec.String
import Lean.Data.Json.Parser
import MiniKernel.Types
import MiniKernel.PP

namespace Export
namespace Parse

open Std.Internal.Parsec Std.Internal.Parsec.String
open Lean (Json)

structure State where
  stream : IO.FS.Stream
  nameMap : Std.HashMap Nat Name := { (0, .anonymous) }
  levelMap : Std.HashMap Nat Level := { (0, .zero) }
  exprMap : Std.HashMap Nat Expr := {}
  ctorMap : Std.HashMap Name Expr := {}
  decls : Array Declaration := #[]
  /-- When `true`, ignore declarations with parse errors  -/
  liberal : Bool := false

abbrev M := StateT State <| IO

def M.run (x : M α) (stream : IO.FS.Stream) (liberal := false) : IO (α × State) := do
  StateT.run x { stream := stream , liberal }

@[inline]
def fail (msg : String) : M α :=
  throw (.userError msg)

@[inline]
def getName (nidx : Nat) : M Name := do
  let some n := (← get).nameMap[nidx]? | fail s!"Name not found {nidx}"
  return n

@[inline]
def addName (nidx : Nat) (n : Name) : M Unit := do
  modify fun s => { s with nameMap := s.nameMap.insert nidx n }

@[inline]
def getLevel (uidx : Nat) : M Level := do
  let some l := (← get).levelMap[uidx]? | fail s!"Level not found {uidx}"
  return l

@[inline]
def addLevel (uidx : Nat) (l : Level) : M Unit := do
  modify fun s => { s with levelMap := s.levelMap.insert uidx l }

@[inline]
def getExpr (eidx : Nat) : M Expr := do
  let some e := (← get).exprMap[eidx]? | fail s!"Expr not found {eidx}"
  return e

@[inline]
def addExpr (eidx : Nat) (e : Expr) : M Unit := do
  modify fun s => { s with exprMap := s.exprMap.insert eidx e }

/-
Recursor rules are not parsed by us

@[inline]
def getRecursorRule (ridx : Nat) : M Lean.RecursorRule := do
  let some r := (← get).recursorRuleMap[ridx]? | fail s!"RecursorRule not found {ridx}"
  return r

@[inline]
def addRecursorRule (ridx : Nat) (r : Lean.RecursorRule) : M Unit := do
  modify fun s => { s with recursorRuleMap := s.recursorRuleMap.insert ridx r }
-/

@[inline]
def addDecl (d : Declaration) : M Unit := do
  modify fun s => { s with decls := s.decls.push d }

@[inline]
def parseJsonObj (line : String) : M (Std.TreeMap.Raw String Json) := do
  let .ok (.obj obj) := Json.Parser.anyCore.run line | fail "Expected JSON object"
  return obj

def parseNameStr (json : Json) : M Name := do
  let .obj data := json | fail s!"Name.str invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str invalid"
  let some (.str str) := data["str"]? | fail s!"Name.str invalid"
  return .str (← getName preIdx) str

def parseNameNum (json : Json) : M Name := do
  let .obj data := json | fail s!"Name.num invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str invalid"
  let some (.num (i : Nat)) := data["i"]? | fail s!"Name.num invalid"
  return .num (← getName preIdx) i

def parseLevelSucc (json : Json) : M Level := do
  let .num (lIdx : Nat) := json | fail s!"Level.succ invalid"
  return .succ (← getLevel lIdx)

def parseLevelMax (json : Json) : M Level := do
  let .arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)] := json
    | fail s!"Level.max invalid"
  return .max (← getLevel lhsIdx) (← getLevel rhsIdx)

def parseLevelImax (json : Json) : M Level := do
  let .arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)] := json
    | fail s!"Level.imax invalid"
  return .imax (← getLevel lhsIdx) (← getLevel rhsIdx)

def parseLevelParam (json : Json) : M Level := do
  let .num (nIdx : Nat) := json | fail s!"Level.param invalid"
  return .param (← getName nIdx)

def parseExprBVar (json : Json) : M Expr := do
  let .num (deBruijnIndex : Nat) := json | fail s!"Expr.bvar invalid"
  return .bvar deBruijnIndex

def parseExprSort (json : Json) : M Expr := do
  let .num (uIdx : Nat) := json | fail s!"Expr.sort invalid"
  return .sort (← getLevel uIdx)

def parseExprConst (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.const invalid"
  let some (.num (declNameIdx : Nat)) := data["name"]? | fail s!"Expr.const invalid"
  let some (.arr usIdxs) := data["us"]? | fail s!"Expr.const invalid"

  let declName ← getName declNameIdx
  let us ← usIdxs.mapM fun uIdx => do
    let (.num (uIdx : Nat)) := uIdx | fail s!"Expr.const invalid"
    getLevel uIdx

  return .const declName us.toList

def parseExprApp (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.app invalid"
  let some (.num (fnIdx : Nat)) := data["fn"]? | fail s!"Expr.app invalid"
  let some (.num (argIdx : Nat)) := data["arg"]? | fail s!"Expr.app invalid"
  let fn ← getExpr fnIdx
  let arg ← getExpr argIdx

  return .app fn arg

/-
def parseBinderInfo (info : String) : M BinderInfo :=
  match info with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | _ => fail s!"Invalid binder info: {info}"
-/

def parseExprLam (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.lam invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.lam invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.lam invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.lam invalid"
  let some (.str _binderInfoStr) := data["binderInfo"]? | fail s!"Expr.lam invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx
  -- let binderInfo ← parseBinderInfo binderInfoStr

  return .lam binderName binderType body

def parseExprForallE (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.forallE invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.forallE invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.forallE invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.forallE invalid"
  let some (.str _binderInfoStr) := data["binderInfo"]? | fail s!"Expr.forallE invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx

  return .forall binderName binderType body

def parseExprLetE (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.letE invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.letE invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.letE invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"Expr.letE invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.letE invalid"
  let some (.bool _nondep) := data["nondep"]? | fail s!"Expr.letE invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let value ← getExpr valueIdx
  let body ← getExpr bodyIdx

  return .let binderName binderType value body

def parseExprProj (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.proj invalid"
  let some (.num (typeNameIdx : Nat)) := data["typeName"]? | fail s!"Expr.proj invalid"
  let some (.num (projIdx : Nat)) := data["idx"]? | fail s!"Expr.proj invalid"
  let some (.num (structIdx : Nat)) := data["struct"]? | fail s!"Expr.proj invalid"

  let typeName ← getName typeNameIdx
  let struct ← getExpr structIdx

  return .proj typeName projIdx struct

def parseExprNatLit (json : Json) : M Expr := do
  let .str natValStr := json | fail s!"Expr.lit natVal invalid"
  let some natVal := String.toNat? natValStr | fail s!"Expr.lit natVal invalid"

  return .natLit natVal

def parseExprStrLit (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.lit strVal invalid"
  let some (.str strVal) := data["strVal"]? | fail s!"Expr.lit strVal invalid"
  return .strLit strVal

def parseExprMdata (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.mdata invalid"
  let some (.num (exprIdx : Nat)) := data["expr"]? | fail s!"Expr.mdata invalid"
  let some (.obj _dataObj) := data["data"]? | fail s!"Expr.mdata invalid"
  let expr ← getExpr exprIdx

  return expr

def getNameList (idxs : Array Json) : M (List Name) := do
  idxs.toList.mapM fun idx => do
    let (.num (idx : Nat)) := idx | fail s!"failed to convert to name idx"
    getName idx

def parseAxiomInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"axiomInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"axiomInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"axiomInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"axiomInfo invalid"
  if isUnsafe then
    fail "Unsafe axioms not supported"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx

  addDecl <| .axiom name levelParams type

def parseDefnInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"defnInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"defnInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"defnInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"defnInfo invalid"
  let some _hints := data["hints"]? | fail s!"defnInfo invalid"
  let some (.str safetyStr) := data["safety"]? | fail s!"defnInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"defnInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  match safetyStr with
  | "unsafe" => fail "Unsafe definitions not supported"
  | "safe" => pure ()
  | "partial" => fail "Unsafe definitions not supported"
  | _ => fail s!"Unknown safety parameter: {safetyStr}"
  let _all ← getNameList allIdxs

  addDecl <| .def name levelParams type value .def

def parseThmInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"thmInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"thmInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"thmInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"thmInfo invalid"
  let some (.arr _allIdxs) := data["all"]? | fail s!"thmInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  -- let all ← getNameList allIdxs

  addDecl <| .def name levelParams type value .theorem

def parseOpaqueInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"opaqueInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"opaqueInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"opaqueInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"opaqueInfo invalid"
  -- Work around until the exporter always includes isUnsafe
  let (.bool isUnsafe) := data["isUnsafe"]?.getD (.bool false) | fail s!"axiomInfo invalid"
  let some (.arr _allIdxs) := data["all"]? | fail s!"opaqueInfo invalid"

  if isUnsafe then
    fail "Unsafe opaque definitions not supported"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  -- let all ← getNameList allIdxs

  addDecl <| .def name levelParams type value .opaque

def parseQuotInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (_nameIdx : Nat)) := data["name"]? | fail s!"quotInfo invalid"
  let some (.arr _levelParamsIdxs) := data["levelParams"]? | fail s!"quotInfo invalid"
  let some (.num (_typeIdx : Nat)) := data["type"]? | fail s!"quotInfo invalid"
  let some (.str kindStr) := data["kind"]? | fail s!"quotInfo invalid"

  -- let name ← getName nameIdx
  -- let levelParams ← getNameList levelParamsIdxs
  -- let type ← getExpr typeIdx

  -- We only add it when we see the `type` kind
  match kindStr with
  | "type" => addDecl .quot
  | "ctor" => pure ()
  | "lift" => pure ()
  | "ind" => pure ()
  | _ => fail s!"unknown quot kind: {kindStr}"

def parseInductInfo (json : Json) : M Unit := do
  let .obj data := json | fail "inductInfo invalid: Expected JSON object"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"inductInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"inductInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"inductInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"inductInfo invalid"
  let some (.num (numIndices : Nat)) := data["numIndices"]? | fail s!"inductInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"inductInfo invalid"
  let some (.arr ctorsIdxs) := data["ctors"]? | fail s!"inductInfo invalid"
  let some (.num (numNested : Nat)) := data["numNested"]? | fail s!"inductInfo invalid"
  let some (.bool _isRec) := data["isRec"]? | fail s!"inductInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"inductInfo invalid"
  let some (.bool _isReflexive) := data["isReflexive"]? | fail s!"inductInfo invalid"

  let name ← getName nameIdx

  if isUnsafe then fail s!"Unsafe inductive {pp name} not supported"
  if allIdxs.size > 1 then fail s!"Mutual inductive {pp name} not supported"
  if numNested > 0 then fail s!"Nested inductive {pp name} not supported"

  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let ctorNames ← getNameList ctorsIdxs
  let ctors ← ctorNames.toArray.mapM fun ctorName => do
    let some ctorType := (← get).ctorMap[ctorName]?
      | fail s!"Constructor type not found"
    return (ctorName, ctorType)

  addDecl <| .inductive
    name
    levelParams
    numParams
    type
    ctors

def parseCtorInfo (json : Json) : M Unit := do
  let .obj data := json | fail s!"ctorInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"ctorInfo invalid"
  let some (.arr _levelParamsIdxs) := data["levelParams"]? | fail s!"ctorInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"ctorInfo invalid"
  let some (.num (inductIdx : Nat)) := data["induct"]? | fail s!"ctorInfo invalid"
  let some (.num (cidx : Nat)) := data["cidx"]? | fail s!"ctorInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"ctorInfo invalid"
  let some (.num (numFields : Nat)) := data["numFields"]? | fail s!"ctorInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"ctorInfo invalid"

  if isUnsafe then fail "Unsafe inductives are not supported"

  let name ← getName nameIdx
  let expr ← getExpr typeIdx
  modify fun s => { s with ctorMap := s.ctorMap.insert name expr }

def parseRecInfo (_obj : Std.TreeMap.Raw String Json) : M Unit := do
  pure ()

def parseInductive (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.arr types) := data["types"]? | fail s!"Inductive invalid, no `types`"
  let some (.arr ctors) := data["ctors"]? | fail s!"Inductive invalid, no `ctors`"
  let some (.arr _recs) := data["recs"]? | fail s!"Inductive invalid, no `recs`"
  ctors.forM parseCtorInfo
  types.forM parseInductInfo
  -- recs.forM parseRecInfo

def parseItem (line : String) : M Unit := do
  try
    let obj ← parseJsonObj line
    let kv := obj.toList
    -- Normalize key order...
    let kv := match kv with
      | [x, y@("in", _)] => [y,x]
      | [x, y@("ie", _)] => [y,x]
      | [x, y@("il", _)] => [y,x]
      | _ =>kv
    -- so that we can match on it easily
    match kv with
    | [("in", .num (idx : Nat)),("str", data)] =>   addName idx <| ← parseNameStr data
    | [("in", .num (idx : Nat)),("num", data)] =>   addName idx <| ← parseNameNum data
    | [("il", .num (idx : Nat)),("succ", data)] =>  addLevel idx <| ← parseLevelSucc data
    | [("il", .num (idx : Nat)),("max", data)] =>   addLevel idx <| ← parseLevelMax data
    | [("il", .num (idx : Nat)),("imax", data)] =>  addLevel idx <| ← parseLevelImax data
    | [("il", .num (idx : Nat)),("param", data)] => addLevel idx <| ← parseLevelParam data
    | [("ie", .num (idx : Nat)),("bvar", data)] =>  addExpr idx <| ← parseExprBVar data
    | [("ie", .num (idx : Nat)),("sort", data)] =>  addExpr idx <| ← parseExprSort data
    | [("ie", .num (idx : Nat)),("const", data)] => addExpr idx <| ← parseExprConst data
    | [("ie", .num (idx : Nat)),("app", data)] =>   addExpr idx <| ← parseExprApp data
    | [("ie", .num (idx : Nat)),("lam", data)] =>   addExpr idx <| ← parseExprLam data
    | [("ie", .num (idx : Nat)),("forallE", data)] =>addExpr idx <| ← parseExprForallE data
    | [("ie", .num (idx : Nat)),("letE", data)] =>   addExpr idx <| ← parseExprLetE data
    | [("ie", .num (idx : Nat)),("proj", data)] =>   addExpr idx <| ← parseExprProj data
    | [("ie", .num (idx : Nat)),("natVal", data)] => addExpr idx <| ← parseExprNatLit data
    | [("ie", .num (idx : Nat)),("strVal", data)] => addExpr idx <| ← parseExprStrLit data
    | [("ie", .num (idx : Nat)),("mdata", data)] => addExpr idx <| ← parseExprMdata data
    | [("axiom", .obj data)] => parseAxiomInfo data
    | [("def", .obj data)] => parseDefnInfo data
    | [("thm", .obj data)] => parseThmInfo data
    | [("opaque", .obj data)] => parseOpaqueInfo data
    | [("quot", .obj data)] => parseQuotInfo data
    | [("inductive", .obj data)] => parseInductive data
    | _ => fail s!"Unknown export object with keys {obj.keys}"
  catch e =>
    if (← get).liberal then
      pure ()
    else
      throw e

partial def parseItems : M Unit :=
  go
where
  go : M Unit := do
    let line ← (← get).stream.getLine
    unless line.isEmpty do
      parseItem line
      go

def parseMdata : M Unit := do
  let _line ← (← get).stream.getLine

def parseFile : M Unit := do
  parseMdata
  parseItems

end Parse

def parseStream (stream : IO.FS.Stream) (liberal := false) : IO (Array Declaration) := do
  let (_, state) ← Parse.M.run Parse.parseFile stream (liberal := liberal)
  let { decls, .. } := state
  return decls

end Export

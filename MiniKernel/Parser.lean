/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Joachim Breitner
-/
import Std
import Std.Internal.Parsec.String
import Lean.Data.Json.Parser
import MiniKernel.Types

namespace Export
namespace Parse

open Std.Internal.Parsec Std.Internal.Parsec.String
open Lean (Json)

structure State where
  stream : IO.FS.Stream
  nameMap : Std.HashMap Nat Name := { (0, .anonymous) }
  levelMap : Std.HashMap Nat Level := { (0, .zero) }
  exprMap : Std.HashMap Nat Expr := {}
  decls : Array Declaration := #[]

abbrev M := StateT State <| IO

def M.run (x : M α) (stream : IO.FS.Stream) : IO (α × State) := do
  StateT.run x { stream := stream }

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
  modify fun s => {
    s with
      decls := s.decls.push d
    }

@[inline]
def parseJsonObj (line : String) : M (Std.TreeMap.Raw String Json) := do
  let .ok (.obj obj) := Json.Parser.anyCore.run line | fail "Expected JSON object"
  return obj

@[inline]
def fetchIndex (obj : Std.TreeMap.Raw String Json) : M Nat := do
  let some (.num (idx : Nat)) := obj["i"]? | fail s!"Object is missing the index key: {obj.keys}"
  return idx

def parseNameStr (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["str"]? | fail s!"Name.str {idx} invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str {idx} invalid"
  let some (.str str) := data["str"]? | fail s!"Name.str {idx} invalid"

  let pre ← getName preIdx

  addName idx (.str pre str)

def parseNameNum (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["num"]? | fail s!"Name.num {idx} invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str {idx} invalid"
  let some (.num (i : Nat)) := data["i"]? | fail s!"Name.num {idx} invalid"

  let pre ← getName preIdx

  addName idx (.num pre i)

def parseLevelSucc (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.num (lIdx : Nat)) := obj["succ"]? | fail s!"Level.succ {idx} invalid"
  let l ← getLevel lIdx

  addLevel idx (.succ l)

def parseLevelMax (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)]) := obj["max"]?
    | fail s!"Level.max {idx} invalid"

  let lhs ← getLevel lhsIdx
  let rhs ← getLevel rhsIdx

  addLevel idx (.max lhs rhs)

def parseLevelImax (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)]) := obj["imax"]?
    | fail s!"Level.imax {idx} invalid"

  let lhs ← getLevel lhsIdx
  let rhs ← getLevel rhsIdx

  addLevel idx (.imax lhs rhs)

def parseLevelParam (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.num (nIdx : Nat)) := obj["param"]? | fail s!"Level.param {idx} invalid"

  let n ← getName nIdx

  addLevel idx (.param n)

def parseExprBVar (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["bvar"]? | fail s!"Expr.bvar {idx} invalid"
  let some (.num (deBruijnIndex : Nat)) := data["deBruijnIndex"]? | fail s!"Expr.bvar {idx} invalid"

  addExpr idx (.bvar deBruijnIndex)

def parseExprSort (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["sort"]? | fail s!"Expr.sort {idx} invalid"
  let some (.num (uIdx : Nat)) := data["u"]? | fail s!"Expr.sort {idx} invalid"

  let u ← getLevel uIdx

  addExpr idx (.sort u)

def parseExprConst (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["const"]? | fail s!"Expr.const {idx} invalid"
  let some (.num (declNameIdx : Nat)) := data["declName"]? | fail s!"Expr.const {idx} invalid"
  let some (.arr usIdxs) := data["us"]? | fail s!"Expr.const {idx} invalid"

  let declName ← getName declNameIdx
  let us ← usIdxs.mapM fun uIdx => do
    let (.num (uIdx : Nat)) := uIdx | fail s!"Expr.const {idx} invalid"
    getLevel uIdx

  addExpr idx (.const declName us.toList)

def parseExprApp (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["app"]? | fail s!"Expr.app {idx} invalid"
  let some (.num (fnIdx : Nat)) := data["fn"]? | fail s!"Expr.app {idx} invalid"
  let some (.num (argIdx : Nat)) := data["arg"]? | fail s!"Expr.app {idx} invalid"

  let fn ← getExpr fnIdx
  let arg ← getExpr argIdx

  addExpr idx (.app fn arg)

def parseExprLam (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["lam"]? | fail s!"Expr.lam {idx} invalid"
  let some (.num (binderNameIdx : Nat)) := data["binderName"]? | fail s!"Expr.lam {idx} invalid"
  let some (.num (binderTypeIdx : Nat)) := data["binderType"]? | fail s!"Expr.lam {idx} invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.lam {idx} invalid"
  -- let some (.str binderInfoStr) := data["binderInfo"]? | fail s!"Expr.lam {idx} invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx

  addExpr idx (.lam binderName binderType body)

def parseExprForallE (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["forallE"]? | fail s!"Expr.forallE {idx} invalid"
  let some (.num (binderNameIdx : Nat)) := data["binderName"]? | fail s!"Expr.forallE {idx} invalid"
  let some (.num (binderTypeIdx : Nat)) := data["binderType"]? | fail s!"Expr.forallE {idx} invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.forallE {idx} invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx

  addExpr idx (.forall binderName binderType body)

def parseExprLetE (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["letE"]? | fail s!"Expr.letE {idx} invalid"
  let some (.num (binderNameIdx : Nat)) := data["declName"]? | fail s!"Expr.letE {idx} invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.letE {idx} invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"Expr.letE {idx} invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.letE {idx} invalid"
  -- let some (.bool nondep) := data["nondep"]? | fail s!"Expr.letE {idx} invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let value ← getExpr valueIdx
  let body ← getExpr bodyIdx

  addExpr idx (.let binderName binderType value body)

def parseExprProj (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["proj"]? | fail s!"Expr.proj {idx} invalid"
  let some (.num (typeNameIdx : Nat)) := data["typeName"]? | fail s!"Expr.proj {idx} invalid"
  let some (.num (projIdx : Nat)) := data["idx"]? | fail s!"Expr.proj {idx} invalid"
  let some (.num (structIdx : Nat)) := data["struct"]? | fail s!"Expr.proj {idx} invalid"

  let typeName ← getName typeNameIdx
  let struct ← getExpr structIdx

  addExpr idx (.proj typeName projIdx struct)

def parseExprNatLit (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.str natValStr) := obj["natVal"]? | fail s!"Expr.lit natVal {idx} invalid"
  let some natVal := String.toNat? natValStr | fail s!"Expr.lit natVal {idx} invalid"

  addExpr idx (.natLit natVal)

def parseExprStrLit (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.str strVal) := obj["strVal"]? | fail s!"Expr.lit strVal {idx} invalid"

  addExpr idx (.strLit strVal)

def getNameList (idxs : Array Json) : M (List Name) := do
  idxs.toList.mapM fun idx => do
    let (.num (idx : Nat)) := idx | fail s!"failed to convert to name idx"
    getName idx

def parseAxiomInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["axiomInfo"]? | fail s!"axiomInfo invalid"
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

def parseDefnInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["defnInfo"]? | fail s!"defnInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"defnInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"defnInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"defnInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"defnInfo invalid"
  -- let some hints := data["hints"]? | fail s!"defnInfo invalid"
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

def parseThmInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["thmInfo"]? | fail s!"thmInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"thmInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"thmInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"thmInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"thmInfo invalid"
  -- let some (.arr allIdxs) := data["all"]? | fail s!"thmInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  -- let all ← getNameList allIdxs

  addDecl <| .def name levelParams type value .theorem

def parseOpaqueInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["opaqueInfo"]? | fail s!"opaqueInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"opaqueInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"opaqueInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"opaqueInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"opaqueInfo invalid"
  -- Work around until the exporter always includes isUnsafe
  let (.bool isUnsafe) := data["isUnsafe"]?.getD (.bool false) | fail s!"axiomInfo invalid"
  if isUnsafe then
    fail "Unsafe opaque definitions not supported"
  -- let some (.arr allIdxs) := data["all"]? | fail s!"opaqueInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  -- let all ← getNameList allIdxs

  addDecl <| .def name levelParams type value .opaque

def parseQuotInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["quotInfo"]? | fail s!"quotInfo invalid"
  -- let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"quotInfo invalid"
  -- let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"quotInfo invalid"
  -- let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"quotInfo invalid"
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

def parseInductInfo (_obj : Std.TreeMap.Raw String Json) : M Unit := do
  fail "Inductive types not yet supported"
  /-
  let some (.obj data) := obj["inductInfo"]? | fail s!"inductInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"inductInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"inductInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"inductInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"inductInfo invalid"
  let some (.num (numIndices : Nat)) := data["numIndices"]? | fail s!"inductInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"inductInfo invalid"
  let some (.arr ctorsIdxs) := data["ctors"]? | fail s!"inductInfo invalid"
  let some (.num (numNested : Nat)) := data["numNested"]? | fail s!"inductInfo invalid"
  let some (.bool isRec) := data["isRec"]? | fail s!"inductInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"inductInfo invalid"
  let some (.bool isReflexive) := data["isReflexive"]? | fail s!"inductInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let all ← getNameList allIdxs
  let ctors ← getNameList ctorsIdxs

  addDecl name <| .inductInfo {
    name,
    levelParams,
    type,
    numParams,
    numIndices,
    all,
    ctors,
    numNested,
    isRec,
    isUnsafe,
    isReflexive,
  }
  -/

def parseCtorInfo (_obj : Std.TreeMap.Raw String Json) : M Unit := do
  pure ()

def parseRecInfo (_obj : Std.TreeMap.Raw String Json) : M Unit := do
  pure ()

def parseItem (line : String) : M Unit := do
  let obj ← parseJsonObj line
  if obj.contains "str" then
    parseNameStr obj
  else if obj.contains "num" then
    parseNameNum obj
  else if obj.contains "succ" then
    parseLevelSucc obj
  else if obj.contains "max" then
    parseLevelMax obj
  else if obj.contains "imax" then
    parseLevelImax obj
  else if obj.contains "param" then
    parseLevelParam obj
  else if obj.contains "bvar" then
    parseExprBVar obj
  else if obj.contains "sort" then
    parseExprSort obj
  else if obj.contains "const" then
    parseExprConst obj
  else if obj.contains "app" then
    parseExprApp obj
  else if obj.contains "lam" then
    parseExprLam obj
  else if obj.contains "forallE" then
    parseExprForallE obj
  else if obj.contains "letE" then
    parseExprLetE obj
  else if obj.contains "proj" then
    parseExprProj obj
  else if obj.contains "natVal" then
    parseExprNatLit obj
  else if obj.contains "strVal" then
    parseExprStrLit obj
  else if obj.contains "mdata" then
    fail "Metadata not yet supported"
  else if obj.contains "axiomInfo" then
    parseAxiomInfo obj
  else if obj.contains "defnInfo" then
    parseDefnInfo obj
  else if obj.contains "thmInfo" then
    parseThmInfo obj
  else if obj.contains "opaqueInfo" then
    parseOpaqueInfo obj
  else if obj.contains "quotInfo" then
    parseQuotInfo obj
  else if obj.contains "inductInfo" then
    parseInductInfo obj
  else if obj.contains "ctorInfo" then
    parseCtorInfo obj
  else if obj.contains "recInfo" then
    parseRecInfo obj
  else
    fail s!"Unknown export object: {obj.keys}"


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

def parseStream (stream : IO.FS.Stream) : IO (Array Declaration) := do
  let (_, state) ← Parse.M.run Parse.parseFile stream
  let { decls, .. } := state
  return decls

end Export

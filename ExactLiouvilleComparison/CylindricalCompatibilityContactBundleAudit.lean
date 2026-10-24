module
public import Lean
import all Lean.Elab.Idbg

public section

/-! Evidence tooling only; no mathematical module imports this file.
A JSON-lines DAG of exact Expr nodes. Immediate child expressions in each node
are encoded as bvar node indices; actual bvar nodes retain their de Bruijn index.
Each emitted JSON line is parsed, decoded using already decoded children, and
compared by Expr.equal with the original. Metadata is rejected, never stripped.
-/
namespace ContactBundleAudit
open Lean

structure State where
  seen : ExprStructMap Nat := {}
  decoded : Array Expr := #[]

def child (nodes : Array Expr) : Expr → Except String Expr
  | .bvar i => match nodes[i]? with
    | some e => .ok e
    | none => .error "Invalid DAG child index"
  | _ => .error "Invalid DAG child reference"

def restore (nodes : Array Expr) (e : Expr) : Except String Expr := do
  match e with
  | .app f a => return .app (← child nodes f) (← child nodes a)
  | .lam n t b bi => return .lam n (← child nodes t) (← child nodes b) bi
  | .forallE n t b bi => return .forallE n (← child nodes t) (← child nodes b) bi
  | .letE n t v b nd => return .letE n (← child nodes t) (← child nodes v) (← child nodes b) nd
  | .proj n i s => return .proj n i (← child nodes s)
  | .mdata .. => .error "Metadata unsupported: refusing lossy export"
  | _ => return e

partial def emit (out : IO.FS.Handle) (e : Expr) : StateT State IO Nat := do
  if let some i := (← get).seen[(⟨e⟩ : ExprStructEq)]? then return i
  let shallow : Expr ← match e with
    | .app f a => do pure <| Expr.app (.bvar (← emit out f)) (.bvar (← emit out a))
    | .lam n t b bi => do pure <| Expr.lam n (.bvar (← emit out t)) (.bvar (← emit out b)) bi
    | .forallE n t b bi => do pure <| Expr.forallE n (.bvar (← emit out t)) (.bvar (← emit out b)) bi
    | .letE n t v b nd => do pure <| Expr.letE n (.bvar (← emit out t)) (.bvar (← emit out v)) (.bvar (← emit out b)) nd
    | .proj n i s => do pure <| Expr.proj n i (.bvar (← emit out s))
    | .mdata .. => throw <| IO.userError "Metadata unsupported: refusing lossy export"
    | .mvar .. | .fvar .. => throw <| IO.userError "Unresolved variable in export"
    | _ => pure e
  let st : State ← get
  let i := st.decoded.size
  let line := (Json.mkObj [("node", toJson i), ("expr", Idbg.exprToJson shallow)]).compress
  let parsed ← IO.ofExcept (Json.parse line)
  let parsedId : Nat ← IO.ofExcept (fromJson? (← IO.ofExcept (parsed.getObjVal? "node")))
  let parsedExpr ← IO.ofExcept (Idbg.exprFromJson? (← IO.ofExcept (parsed.getObjVal? "expr")))
  let decoded ← IO.ofExcept (restore st.decoded parsedExpr)
  unless parsedId == i && Expr.equal e decoded do
    throw <| IO.userError "Serialized expression DAG roundtrip mismatch"
  out.putStrLn line
  set ({ seen := st.seen.insert ⟨e⟩ i, decoded := st.decoded.push decoded } : State)
  return i

def declaration (out : IO.FS.Handle) (info : ConstantInfo) (body : Bool)
    (state : State) : IO State := do
  if info.type.hasMVar || info.type.hasFVar || info.type.hasLooseBVars then
    throw <| IO.userError "Nonclosed elaborated declaration type"
  let (root, state) ← (emit out info.type).run state
  let (value, state) ← if body then
    match info.value? with
    | some v => do
      let (root, state) ← (emit out v).run state
      pure (toJson root, state)
    | none => pure (Json.null, state)
    else pure (Json.null, state)
  let line := (Json.mkObj [("declaration", Idbg.nameToJson info.name),
    ("display_name", toJson info.name.toString),
    ("level_params", toJson (info.levelParams.map Idbg.nameToJson)),
    ("type_root", toJson root), ("value_root", value)]).compress
  let parsed ← IO.ofExcept (Json.parse line)
  let name ← IO.ofExcept (Idbg.nameFromJson? (← IO.ofExcept (parsed.getObjVal? "declaration")))
  let params : List Json ← IO.ofExcept (fromJson? (← IO.ofExcept (parsed.getObjVal? "level_params")))
  let params ← IO.ofExcept (params.mapM Idbg.nameFromJson?)
  unless name == info.name && params == info.levelParams do
    throw <| IO.userError "Declaration identity/universe roundtrip mismatch"
  out.putStrLn line
  out.flush
  return state

end ContactBundleAudit

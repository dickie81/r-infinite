import Lean
open Lean

/-! Read the olean of every module named in the list file (no environment is built, so modules whose
constant names clash can all be read). Print, as JSON lines:
  {"module": m, "imports": [...]}                                  one per module
  {"name": n, "module": m, "kind": k, "tdeps": [...], "vdeps": [...], "th": h, "vh": h2}   one per constant
where tdeps/vdeps are the constants used in the type/value that are declared in one of the listed modules,
th is the hash of the type and vh the hash of the value (0 for none). Then
  {"dupof": [names...]}  for every group of two or more theorems (resp. definitions) whose types (and, for
                         definitions, values) are equal as expressions. -/

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let listFile := args[0]!
  let outPath := args[1]!
  let mods := ((← IO.FS.lines listFile).filter (· ≠ "")).map String.toName
  let h ← IO.FS.Handle.mk outPath .write
  -- pass 1: owners
  let mut owner : Std.HashMap Name Name := {}
  let mut datas : Array (Name × ModuleData) := #[]
  for m in mods do
    let f ← findOLean m
    let (md, _) ← readModuleData f
    datas := datas.push (m, md)
    for n in md.constNames do
      if !owner.contains n then owner := owner.insert n m
    h.putStrLn (Json.mkObj [("module", toJson (toString m)),
      ("imports", toJson (md.imports.map (fun i => toString i.module)))]).compress
  -- pass 2: constants
  let mut byType : Std.HashMap UInt64 (Array (Name × Expr × Option Expr × String)) := {}
  let mut count := 0
  for (m, md) in datas do
    for ci in md.constants do
      let n := ci.name
      let filt (e : Expr) : Array String :=
        (e.getUsedConstants.filter (fun d => d != n && owner.contains d)).map toString
      let v := valueOf? ci
      let td := filt ci.type
      let vd := match v with | some e => filt e | none => #[]
      let vh : UInt64 := match v with | some e => e.hash | none => 0
      h.putStrLn (Json.mkObj [("name", toJson (toString n)), ("module", toJson (toString m)),
        ("kind", toJson (kindOf ci)), ("tdeps", toJson td), ("vdeps", toJson vd),
        ("th", toJson ci.type.hash.toNat), ("vh", toJson vh.toNat)]).compress
      count := count + 1
      let k := kindOf ci
      if (k == "theorem" || k == "def") && !n.isInternal then
        let key := mixHash ci.type.hash (if k == "def" then vh else 0)
        byType := byType.insert key ((byType.getD key #[]).push (n, ci.type, (if k == "def" then v else none), toString m))
  -- duplicate groups (exact expression equality)
  let mut ngroups := 0
  for (_, arr) in byType.toList do
    if arr.size < 2 then continue
    let mut rest := arr
    while rest.size > 1 do
      let (n0, t0, v0, m0) := rest[0]!
      let same := rest.filter (fun (_, t, v, _) => t == t0 && v == v0)
      if same.size > 1 then
        ngroups := ngroups + 1
        h.putStrLn (Json.mkObj [("dupof", toJson (same.map (fun (n, _, _, m) => toString n ++ " @ " ++ m)))]).compress
      rest := rest.filter (fun (_, t, v, _) => !(t == t0 && v == v0))
      let _ := n0; let _ := m0
  h.flush
  IO.println s!"modules {mods.size}, constants {count}, duplicate groups {ngroups}"

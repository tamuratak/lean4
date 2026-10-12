/-
Copyright (c) 2026 Takashi Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takashi Tamura
-/
module

prelude
public import Lean.Compiler.LCNF.Internalize
public import Lean.Compiler.LCNF.PassManager

public section

namespace Lean.Compiler.LCNF
namespace ScalarArgs

-- Keep the transformation bounded and preserve the original calling convention with a wrapper.
private partial def scalarLeaves (type : Expr) : Option Nat := do
  if type.getAppFn.constName? == some ``Prod then
    let args := type.getAppArgs
    guard (args.size == 2)
    let count := (← scalarLeaves args[0]!) + (← scalarLeaves args[1]!)
    guard (count ≤ 16)
    return count
  else
    guard ([``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Float, ``Float32].contains
      (type.getAppFn.constName?.getD .anonymous))
    return 1

private def shouldSplit (type : Expr) : Bool :=
  type.getAppFn.constName? == some ``Prod && (scalarLeaves type).isSome

private partial def unpack (type : Expr) (arg : Arg .pure) :
    CompilerM (Array (LetDecl .pure) × Array (Arg .pure)) := do
  unless shouldSplit type do return (#[], #[arg])
  let .fvar base := arg | unreachable!
  let types := type.getAppArgs
  let fst ← mkLetDecl `_fst types[0]! (.proj ``Prod 0 base)
  let snd ← mkLetDecl `_snd types[1]! (.proj ``Prod 1 base)
  let (fstLets, fstArgs) ← unpack types[0]! (.fvar fst.fvarId)
  let (sndLets, sndArgs) ← unpack types[1]! (.fvar snd.fvarId)
  return (#[fst, snd] ++ fstLets ++ sndLets, fstArgs ++ sndArgs)

private partial def pack (type : Expr) (name : Name) :
    CompilerM (Array (Param .pure) × Array (LetDecl .pure) × Arg .pure) := do
  unless shouldSplit type do
    let param ← mkParam name type false
    return (#[param], #[], .fvar param.fvarId)
  let types := type.getAppArgs
  let (fstParams, fstLets, fst) ← pack types[0]! (name.str "fst")
  let (sndParams, sndLets, snd) ← pack types[1]! (name.str "snd")
  let decl ← mkLetDecl name type (.const ``Prod.mk [] #[.erased, .erased, fst, snd])
  return (fstParams ++ sndParams, fstLets ++ sndLets |>.push decl, .fvar decl.fvarId)

private def attach (decls : Array (LetDecl .pure)) (code : Code .pure) : Code .pure :=
  decls.foldr (fun decl code => .let decl code) code

private def expandArgs (params : Array (Param .pure)) (args : Array (Arg .pure)) :
    CompilerM (Array (LetDecl .pure) × Array (Arg .pure)) := do
  let mut lets := #[]
  let mut expanded := #[]
  for param in params, arg in args do
    let (newLets, newArgs) ← unpack param.type arg
    lets := lets ++ newLets
    expanded := expanded ++ newArgs
  return (lets, expanded ++ args.drop params.size)

private partial def rewriteCalls (code : Code .pure) (name worker : Name)
    (params : Array (Param .pure)) : CompilerM (Code .pure) := do
  match code with
  | .let decl k =>
    let k ← rewriteCalls k name worker params
    if let .const callee _ args := decl.value then
      if callee == name then
        let (lets, args) ← expandArgs params args
        let decl ← decl.updateValue (.const worker [] args)
        return attach lets (.let decl k)
    return code.updateLet! decl k
  | .fun decl k | .jp decl k =>
    let decl ← decl.updateValue (← rewriteCalls decl.value name worker params)
    return code.updateFun! decl (← rewriteCalls k name worker params)
  | .cases cases =>
    let alts ← cases.alts.mapMonoM fun alt =>
      return alt.updateCode (← rewriteCalls alt.getCode name worker params)
    return code.updateAlts! alts
  | .return .. | .jmp .. | .unreach .. => return code

private def canRewrite (decl : Decl .pure) (code : Code .pure) : Bool := Id.run do
  let check : StateM (Bool × Bool) Unit := code.forM fun code => do
    let .let { value := .const name _ args, .. } .. := code | return
    if name != decl.name then return
    modify fun (_, valid) => (true, valid && args.size ≥ decl.params.size)
    for param in decl.params, arg in args do
      if shouldSplit param.type && !(arg matches .fvar _) then
        modify fun (found, _) => (found, false)
  let (_, found, valid) := check.run (false, true)
  return found && valid

def transform (decl : Decl .pure) : CompilerM (Array (Decl .pure)) := do
  let .code code := decl.value | return #[decl]
  unless decl.recursive && decl.params.any (shouldSplit ·.type) && canRewrite decl code do
    return #[decl]
  let expandedArity := decl.params.foldl (init := 0) fun count param =>
    count + if shouldSplit param.type then (scalarLeaves param.type).getD 1 else 1
  if expandedArity > 32 then return #[decl]
  let workerName := decl.name ++ `_scalarArgs
  let mut params := #[]
  let mut lets := #[]
  let mut subst : FVarSubst .pure := {}
  for param in decl.params do
    if shouldSplit param.type then
      let (fields, bindings, arg) ← pack param.type param.binderName
      params := params ++ fields
      lets := lets ++ bindings
      subst := subst.insert param.fvarId arg
    else
      params := params.push param
  let code ← rewriteCalls code decl.name workerName decl.params
  let code ← code.internalize subst
  let code := attach lets code
  let type ← mkForallParams params (← code.inferType)
  let worker := { decl with name := workerName, params, type, value := .code code }
  worker.saveMono
  let mkWrapper : Internalize.InternalizeM .pure (Decl .pure) := do
    let params ← decl.params.mapM Internalize.internalizeParam
    let (lets, args) ← expandArgs params (params.map (·.toArg))
    let call ← mkAuxLetDecl (.const workerName [] args)
    let value := .code (attach lets (.let call (.return call.fvarId)))
    return { decl with params, value, inlineAttr? := some .inline, recursive := false }
  let wrapper ← mkWrapper.run' {}
  wrapper.saveMono
  return #[worker, wrapper]

end ScalarArgs

def scalarArgs : Pass where
  phase := .mono
  phaseOut := .mono
  name := `scalarArgs
  run decls := decls.foldlM (init := #[]) fun result decl =>
    return result ++ (← ScalarArgs.transform decl)

builtin_initialize registerTraceClass `Compiler.scalarArgs (inherited := true)

end Lean.Compiler.LCNF

/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Instances
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# Application lemmas for bundled handlers

A handler built by the constructor of a one-field function structure, such as `QueryImpl`, is
used through the equation for its application, as bundled morphisms are in Mathlib. Unfolding the
handler instead makes `simp` traverse its whole body at every occurrence. This environment linter
reports such a definition when it has no application lemma (`@[simps]` generates one) and when it
is reducible, since `simp` unfolds reducible definitions without consulting their lemmas.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace ToMathlib.Lint

/-- The function structures whose constructed values need application lemmas, each with the
projection that applies it. -/
private def handlerStructures : List (Name × Name) :=
  [(`QueryImpl, `QueryImpl.toFun), (`PFunctor.Handler, `PFunctor.Handler.toFun)]

/-- The projection of `declName`'s structure if `declName` is a definition whose value, under its
parameters, is a handler structure's constructor applied to all its arguments. -/
private def constructedHandler? (declName : Name) : MetaM (Option Name) := do
  let .defnInfo info ← getConstInfo declName | return none
  lambdaTelescope info.value fun _ body => do
    let body := body.consumeMData
    let .const c _ := body.getAppFn | return none
    let some (.ctorInfo ctor) := (← getEnv).find? c | return none
    if body.getAppNumArgs < ctor.numParams + ctor.numFields then return none
    return handlerStructures.lookup ctor.induct

/-- Whether the conclusion of `type` is an equation whose left side applies `declName` or is an
instance of it. -/
private def isApplicationEquation (declName proj : Name) (type : Expr) : Bool :=
  match type.getForallBody.eq? with
  | some (_, lhs, _) => lhs.getAppFn.isConstOf declName || (lhs.find? fun e =>
      e.isAppOf proj && e.getAppArgs.any (·.getAppFn.isConstOf declName)).isSome
  | none => false

/-- Whether `declName` has an application lemma: a theorem of its own module named after it, or a
`simp` lemma, whose left side applies it. -/
private def hasApplicationLemma (declName proj : Name) : MetaM Bool := do
  let env ← getEnv
  let .str p s := declName | return false
  if let some idx := env.getModuleIdxFor? declName then
    for n in env.header.moduleData[idx.toNat]!.constNames do
      let .str q t := n | continue
      if q == p && (s ++ "_").isPrefixOf t then
        if let some (.thmInfo thm) := env.find? n then
          if isApplicationEquation declName proj thm.type then return true
  let c ← mkConstWithFreshMVarLevels declName
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType c)
  let e ← try mkAppM proj #[mkAppN c args] catch _ => return false
  let (ts, _, _) ← forallMetaTelescopeReducing (← inferType e)
  let some t := ts[0]? | return false
  for thm in ← (← getSimpTheorems).post.getUnify (mkApp e t) do
    if isApplicationEquation declName proj (← inferType (← thm.getValue)) then return true
  return false

/-- Report handlers built by a structure constructor that have no application lemma or are
reducible. -/
@[env_linter] def handlerApply : Linter where
  noErrorsFound := "Every constructed handler has an application lemma."
  errorsFound := "HANDLERS WITHOUT APPLICATION LEMMAS."
  test declName := do
    if (← isAutoDecl declName) || (← isInstance declName) then return none
    let some proj ← constructedHandler? declName | return none
    if ← isReducible declName then
      return m!"is reducible, so `simp` unfolds it instead of using its application lemmas"
    if ← hasApplicationLemma declName proj then return none
    return m!"has no application lemma; add `@[simps]` or state its equations"

end ToMathlib.Lint

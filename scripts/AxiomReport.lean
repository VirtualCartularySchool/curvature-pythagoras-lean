import Lean
import PythagoreanPaper

/-!
# Axiom report for every module `PythagoreanPaper.*`

Run from the repository root after `lake build`:

    lake env lean scripts/AxiomReport.lean

For every user-written declaration of every module whose name starts with `PythagoreanPaper`, this
prints the axioms the declaration depends on, directly or transitively (the information
`#print axioms` gives). It fails with an error, and hence a non-zero exit status, if

* any declaration of those modules, auxiliary ones included, depends on an axiom outside
  `propext`, `Classical.choice`, `Quot.sound` (a `sorry` or `admit` shows up as `sorryAx`), or
* one of those modules declares an `axiom` of its own (in Lean 4.35 this includes the auxiliary
  axiom that `native_decide` adds).

This reports axiom dependencies only. It does not re-check proofs; the kernel checked them when
`lake build` compiled the modules.
-/

open Lean Elab Command

namespace AxiomReport

/-- The three standard axioms of classical Lean/Mathlib mathematics. -/
def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- A short label for the kind of a constant. -/
def kindLabel : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- `#axiom_report P` audits every constant stored in every imported module whose name has the
prefix `P`. -/
elab "#axiom_report " pfx:ident : command => do
  let env ← getEnv
  let p := pfx.getId
  let mods := env.allImportedModuleNames.filter (p.isPrefixOf ·)
  if mods.isEmpty then
    throwError "no imported module has the prefix `{p}`"
  let mut rows : Array (String × Nat × String) := #[]
  let mut violations : Array String := #[]
  let mut ownAxioms : Array Name := #[]
  let mut used : Array Name := #[]
  let mut total := 0
  for m in mods do
    let some idx := env.getModuleIdx? m | continue
    let data := env.header.moduleData[idx]!
    for n in data.constNames, ci in data.constants do
      total := total + 1
      if ci matches .axiomInfo _ then
        ownAxioms := ownAxioms.push n
      let axs := (← collectAxioms n).qsort Name.lt
      for a in axs do
        unless used.contains a do used := used.push a
      let bad := axs.filter (!allowed.contains ·)
      unless bad.isEmpty do
        violations := violations.push s!"{n} -> {bad.toList}"
      if !n.isInternalDetail then
        if let some r ← findDeclarationRanges? n then
          rows := rows.push (m.toString, r.range.pos.line,
            s!"  {m}:{r.range.pos.line}: {kindLabel ci} {n}: {axs.toList}")
  let sorted := rows.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1))
  let header :=
    s!"axiom report for {mods.size} module(s) with prefix {p}: {sorted.size} user " ++
    s!"declaration(s), {total} stored constant(s) audited"
  let usedLine := s!"axioms used anywhere: {(used.qsort Name.lt).toList}"
  logInfo m!"{header}\n{String.intercalate "\n" (sorted.map (·.2.2)).toList}\n{usedLine}"
  if sorted.isEmpty then
    throwError "no user declarations found under `{p}`"
  unless ownAxioms.isEmpty do
    throwError "modules under `{p}` declare their own axiom(s): {ownAxioms.toList}"
  unless violations.isEmpty do
    throwError "declarations depending on axioms outside {allowed.toList}:\n\
      {String.intercalate "\n" violations.toList}"
  let pass := s!"PASS: no sorryAx and no project axiom; every constant under {p} " ++
    s!"depends only on axioms from {allowed.toList}"
  logInfo m!"{pass}"

end AxiomReport

#axiom_report PythagoreanPaper

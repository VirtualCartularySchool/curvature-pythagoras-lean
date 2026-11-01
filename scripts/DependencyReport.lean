import Lean
import PythagoreanPaper

/-!
# Dependency report for the proof of the Pythagorean theorem (C10.10, §11–12)

Run from the repository root after `lake build`:

    lake env lean scripts/DependencyReport.lean

For a target declaration this prints, from the compiled environment:

* the user-written declarations of `PythagoreanPaper.*` on which its proof depends, directly or
  transitively, grouped by module;
* whether any declaration of the Riemannian part (`PythagoreanPaper.Riemannian.*`,
  `PythagoreanPaper.Sec04Jacobi`) is among them;
* for every such project declaration, the declarations outside the project from a fixed watch list
  (law of cosines, Pythagorean theorem, `sin² + cos² = 1`, angle sum, …) that it uses directly;
* for the declarations of a given module, the declarations from Mathlib's trigonometry and
  Euclidean geometry that they use directly.

`#dependency_check_full` follows every constant, Mathlib included, so it reports whether a
declaration of Mathlib (such as `EuclideanGeometry.law_cos`) occurs anywhere in the proof of the
target, and through which chain of declarations.

This reads dependencies only (the constants occurring in types and proof terms). It checks
nothing about the proofs themselves; `lake build` did that.
-/

open Lean Elab Command

namespace DependencyReport

/-- The module of a constant, if it was imported. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

def isProject (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => (`PythagoreanPaper).isPrefixOf m
  | none => false

/-- Project constants reachable from `start` through project constants. -/
partial def reach (env : Environment) (start : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := [start]
  repeat
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      unless visited.contains n do
        visited := visited.insert n
        if let some ci := env.find? n then
          for m in ci.getUsedConstantsAsSet do
            if isProject env m && !visited.contains m then
              stack := m :: stack
  return visited

/-- Declarations outside the project whose use is reported. -/
def watchList : List Name :=
  [`EuclideanGeometry.law_cos,
   `InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle,
   `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two,
   `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
   `norm_add_sq_eq_norm_sq_add_norm_sq_real,
   `norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
   `norm_sub_sq_eq_norm_sq_add_norm_sq_real,
   `EuclideanGeometry.angle_add_angle_add_angle_eq_pi,
   `Real.sin_sq_add_cos_sq, `Real.cos_sq_add_sin_sq, `Real.sin_sq, `Real.cos_sq',
   `norm_sub_sq_real, `norm_add_sq_real, `real_inner_self_eq_norm_sq,
   `Real.sin_two_mul, `Real.sin_sub, `Real.cos_sub, `Real.cos_two_mul]

/-- Is the constant from Mathlib's trigonometry or Euclidean geometry? -/
def isGeomTrig (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m =>
    let s := m.toString
    s.startsWith "Mathlib.Geometry.Euclidean" ||
      s.startsWith "Mathlib.Analysis.SpecialFunctions.Trigonometric" ||
      s.startsWith "Mathlib.Analysis.InnerProductSpace"
  | none => false

elab "#dependency_report " target:ident modPfx:ident : command => do
  let env ← getEnv
  let t := target.getId
  unless env.contains t do throwError "unknown declaration {t}"
  let deps := reach env t
  let user := deps.toList.filter (fun n => !n.isInternalDetail)
  -- grouped by module
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for n in user do
    let m := (moduleOf env n).getD `current
    byMod := byMod.insert m ((byMod.getD m #[]).push n)
  let mods := byMod.toList.map (·.1) |>.toArray.qsort Name.lt
  let mut lines : Array String := #[s!"target: {t}",
    s!"project declarations used (directly or transitively): {user.length}"]
  for m in mods do
    let ns := (byMod.getD m #[]).qsort Name.lt
    lines := lines.push s!"  {m}: {ns.toList}"
  let riem := user.filter fun n =>
    match moduleOf env n with
    | some m => (`PythagoreanPaper.Riemannian).isPrefixOf m || m == `PythagoreanPaper.Sec04Jacobi
    | none => false
  lines := lines.push s!"declarations of the Riemannian part among them: {riem.length} {riem}"
  -- watch list
  lines := lines.push "watch-list declarations used directly by these project declarations:"
  for n in deps.toList do
    if let some ci := env.find? n then
      let used := ci.getUsedConstantsAsSet
      let hits := watchList.filter used.contains
      unless hits.isEmpty do
        lines := lines.push s!"  {n} -> {hits}"
  -- trigonometry / Euclidean geometry used by the declarations of the given module
  let pfx := modPfx.getId
  lines := lines.push s!"Mathlib trigonometry / Euclidean geometry used directly by declarations of {pfx}:"
  for n in deps.toList do
    if (moduleOf env n) == some pfx && !n.isInternalDetail then
      if let some ci := env.find? n then
        let used := ci.getUsedConstantsAsSet.toList.filter (isGeomTrig env)
        let used := used.toArray.qsort Name.lt
        unless used.isEmpty do
          lines := lines.push s!"  {n}: {used.toList}"
  logInfo (String.intercalate "\n" lines.toList)

/-- `#dependency_check t [n₁, …]` reports, for each `nᵢ`, whether the proof of `t` depends on it
(directly or transitively, through project declarations). -/
elab "#dependency_check " target:ident " [" names:ident,* "]" : command => do
  let env ← getEnv
  let t := target.getId
  unless env.contains t do throwError "unknown declaration {t}"
  let deps := reach env t
  let mut lines : Array String := #[s!"target: {t}"]
  for n in names.getElems do
    let n := n.getId
    unless env.contains n do throwError "unknown declaration {n}"
    lines := lines.push s!"  {if deps.contains n then "uses    " else "does not use"} {n}"
  logInfo (String.intercalate "\n" lines.toList)

/-- All constants reachable from `start` through every constant (Mathlib included), with the
constant through which each was first reached (for printing a chain of uses). -/
def reachAll (env : Environment) (start : Name) : Std.HashMap Name Name := Id.run do
  let mut parent : Std.HashMap Name Name := {}
  parent := parent.insert start start
  let mut queue : Array Name := #[start]
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet do
        unless parent.contains m do
          parent := parent.insert m n
          queue := queue.push m
  return parent

/-- The chain of uses from `start` to `goal` recorded by `reachAll`. -/
def chainTo (parent : Std.HashMap Name Name) (start goal : Name) : List Name := Id.run do
  let mut path : List Name := [goal]
  let mut cur := goal
  let mut fuel := 100000
  while cur != start && fuel > 0 do
    fuel := fuel - 1
    match parent.get? cur with
    | some p => path := p :: path; cur := p
    | none => break
  return path

/-- `#dependency_check_full t [n₁, …]` reports, for each `nᵢ`, whether `nᵢ` occurs anywhere in the
proof of `t` (directly or transitively, through any declaration, Mathlib included), and if so one
chain of declarations from `t` to `nᵢ`. -/
elab "#dependency_check_full " target:ident " [" names:ident,* "]" : command => do
  let env ← getEnv
  let t := target.getId
  unless env.contains t do throwError "unknown declaration {t}"
  let parent := reachAll env t
  let mut lines : Array String :=
    #[s!"target: {t} (declarations in the full dependency closure: {parent.size})"]
  for n in names.getElems do
    let n := n.getId
    if !env.contains n then
      -- a proof can only use declarations of the environment
      lines := lines.push
        s!"  does not use {n} (not in the environment: its module is not imported)"
    else if parent.contains n then
      lines := lines.push s!"  uses         {n}\n      via {chainTo parent t n}"
    else
      lines := lines.push s!"  does not use {n}"
  logInfo (String.intercalate "\n" lines.toList)

/-- `#dependency_require_full t [present: n₁, …] [absent: m₁, …]` checks, over the whole dependency
closure of `t` (Mathlib included), that every `nᵢ` occurs in the proof of `t` and that no `mⱼ`
does; it fails with an error otherwise (used as a check in CI). -/
elab "#dependency_require_full " target:ident " [present: " pres:ident,* "]"
    " [absent: " abs:ident,* "]" : command => do
  let env ← getEnv
  let t := target.getId
  unless env.contains t do throwError "unknown declaration {t}"
  let parent := reachAll env t
  let mut lines : Array String := #[s!"requirement check for {t}:"]
  let mut failures : Array String := #[]
  for n in pres.getElems do
    let n := n.getId
    unless env.contains n do throwError "unknown declaration {n}"
    if parent.contains n then
      lines := lines.push s!"  OK  uses         {n}"
    else
      lines := lines.push s!"  NG  does not use {n}"
      failures := failures.push s!"{n} (required, not used)"
  for n in abs.getElems do
    let n := n.getId
    if !env.contains n then
      -- a proof can only use declarations of the environment
      lines := lines.push
        s!"  OK  does not use {n} (not in the environment: its module is not imported)"
    else if parent.contains n then
      lines := lines.push s!"  NG  uses         {n}\n      via {chainTo parent t n}"
      failures := failures.push s!"{n} (excluded, used)"
    else
      lines := lines.push s!"  OK  does not use {n}"
  logInfo (String.intercalate "\n" lines.toList)
  unless failures.isEmpty do
    throwError "dependency requirement failed for {t}: {failures.toList}"

end DependencyReport

-- C10.10: the proof of the Pythagorean theorem (C10.9)
#dependency_report PythagoreanPaper.sec10_pythagoras PythagoreanPaper.Sec10

-- §12: the chain `Jacobi field ⇒ S_K ⇒ constant-curvature sine law ⇒ K = 0 ⇒ Pythagoras`
#dependency_check PythagoreanPaper.GeodesicTriangle.sine_law
  [PythagoreanPaper.IsGeodesicVariation.isJacobiFieldOn, PythagoreanPaper.sec4_jacobi_eq_S,
   PythagoreanPaper.sec6_jacobi_eq_S, PythagoreanPaper.hasDerivAt_S_mul_polar,
   PythagoreanPaper.cosine_law_normalBall', PythagoreanPaper.GeodesicTriangle.cosine_law,
   PythagoreanPaper.sec9_sine_law_of_cos_law]
#dependency_check PythagoreanPaper.GeodesicTriangle.angles_eq_angleK
  [PythagoreanPaper.sec4_jacobi_eq_S, PythagoreanPaper.GeodesicTriangle.cosine_law,
   PythagoreanPaper.angleK]
#dependency_check PythagoreanPaper.sec9_euclidean_sine_law
  [PythagoreanPaper.sec9_limit, PythagoreanPaper.sec9_sine_law_of_cos_law,
   PythagoreanPaper.angleK_zero_eq_angle, PythagoreanPaper.GeodesicTriangle.sine_law,
   PythagoreanPaper.GeodesicTriangle.angles_eq_angleK, PythagoreanPaper.sec4_jacobi_eq_S]
#dependency_check PythagoreanPaper.sec10_pythagoras
  [PythagoreanPaper.sec9_euclidean_sine_law, PythagoreanPaper.sec10_sine_laws,
   PythagoreanPaper.sec10_double_and_difference, PythagoreanPaper.GeodesicTriangle.sine_law,
   PythagoreanPaper.GeodesicTriangle.angles_eq_angleK, PythagoreanPaper.sec4_jacobi_eq_S,
   PythagoreanPaper.sec6_jacobi_eq_S]

-- The chain of §12 as one formal dependency (`PythagoreanPaper.CurvatureChain`, 2026-11-01):
-- the Pythagorean theorem of §10 for `ℝ²`, with the sine law obtained through the Riemannian layer
#dependency_report PythagoreanPaper.CurvatureChain.sec10_pythagoras PythagoreanPaper.CurvatureChain
#dependency_check PythagoreanPaper.CurvatureChain.sec10_pythagoras
  [PythagoreanPaper.IsGeodesicVariation.isJacobiFieldOn, PythagoreanPaper.sec4_jacobi_eq_S,
   PythagoreanPaper.sec6_jacobi_eq_S, PythagoreanPaper.hasDerivAt_S_mul_polar,
   PythagoreanPaper.cosine_law_normalBall', PythagoreanPaper.GeodesicTriangle.cosine_law,
   PythagoreanPaper.HypPlane.hasConstSectionalCurvature, PythagoreanPaper.HypPlane.exists_triangle,
   PythagoreanPaper.HypPlane.cosine_law, PythagoreanPaper.HypPlane.angles_eq_angleK,
   PythagoreanPaper.sec9_sine_law_of_cos_law, PythagoreanPaper.CurvatureChain.hyperbolic_sine_law,
   PythagoreanPaper.CurvatureChain.sine_law_limit, PythagoreanPaper.continuousAt_angleK,
   PythagoreanPaper.cosine_law_normalBall_G', PythagoreanPaper.GeodesicTriangle.cosine_law_G,
   PythagoreanPaper.GeodesicTriangle.angles_eq_angleK_zero,
   PythagoreanPaper.EuclideanPlane.angle_eq_angleK_zero,
   PythagoreanPaper.CurvatureChain.euclidean_sine_law,
   PythagoreanPaper.sec10_pythagoras_of_sineLaw,
   PythagoreanPaper.angleK_zero_eq_angle, PythagoreanPaper.sec9_euclidean_sine_law,
   PythagoreanPaper.sec9_limit, PythagoreanPaper.sec9_sine_law_near_zero,
   PythagoreanPaper.sec10_pythagoras]
-- over the whole dependency closure, Mathlib included (informational: the inner product is still
-- used, at the level of the tangent spaces and of the model's coordinates, cf. manuscript §11)
#dependency_check_full PythagoreanPaper.CurvatureChain.sec10_pythagoras
  [EuclideanGeometry.law_cos,
   EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle,
   InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle,
   EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two,
   InnerProductGeometry.norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
   InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
   norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
   norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
   norm_add_sq_eq_norm_sq_add_norm_sq_real, norm_sub_sq_eq_norm_sq_add_norm_sq_real,
   EuclideanGeometry.angle_add_angle_add_angle_eq_pi, norm_sub_sq_real, norm_add_sq_real,
   PythagoreanPaper.norm_sq_eq_inner_sq_add_inner_sq, PythagoreanPaper.sec6_metric,
   inner_eq_sum_norm_sq_div_four,
   PythagoreanPaper.sec6_jacobi_eq_S, PythagoreanPaper.HypPlane.exists_triangle]
-- for comparison: the earlier proof of C10.9 (`PythagoreanPaper.Sec10`, unchanged)
#dependency_check_full PythagoreanPaper.sec10_pythagoras
  [EuclideanGeometry.law_cos,
   EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle,
   InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle,
   EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two,
   norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
   EuclideanGeometry.angle_add_angle_add_angle_eq_pi, PythagoreanPaper.sec6_jacobi_eq_S]
-- CI check (fails the job if violated): the chain theorem uses the Riemannian chain and the flat
-- model, and none of Mathlib's law of cosines, Pythagorean theorems, or the earlier law_cos-based
-- identification `angleK_zero_eq_angle` occurs anywhere in its proof
#dependency_require_full PythagoreanPaper.CurvatureChain.sec10_pythagoras
  [present: PythagoreanPaper.sec4_jacobi_eq_S, PythagoreanPaper.sec6_jacobi_eq_S,
   PythagoreanPaper.hasDerivAt_S_mul_polar, PythagoreanPaper.HypPlane.hasConstSectionalCurvature,
   PythagoreanPaper.HypPlane.exists_triangle, PythagoreanPaper.HypPlane.cosine_law,
   PythagoreanPaper.CurvatureChain.hyperbolic_sine_law,
   PythagoreanPaper.GeodesicTriangle.cosine_law_G,
   PythagoreanPaper.EuclideanPlane.angle_eq_angleK_zero]
  [absent: EuclideanGeometry.law_cos,
   EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle,
   InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle,
   EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two,
   InnerProductGeometry.norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
   InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
   norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
   norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
   norm_add_sq_eq_norm_sq_add_norm_sq_real, norm_sub_sq_eq_norm_sq_add_norm_sq_real,
   PythagoreanPaper.angleK_zero_eq_angle, PythagoreanPaper.sec9_euclidean_sine_law]

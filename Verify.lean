import LRXDiameter
import Lean.Util.CollectAxioms

/-! Axiom audit of the publication package.

Every theorem declared in a module of this package (including private and
compiler-generated helper theorems) may depend only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`. The check fails otherwise. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := [`LRX, `Research, `GraphBridge, `GraphLower, `Reachability, `LRXDiameter]
  let mut thms : Nat := 0
  let mut mods : Std.HashSet Name := {}
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless roots.any (·.isPrefixOf mod) do continue
    mods := mods.insert mod
    unless info.isTheorem do continue
    thms := thms + 1
    for ax in (← collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Nonstandard axiom {ax} in {name} (module {mod})"
  logInfo m!"PASS: {thms} theorems in {mods.size} package modules use only propext, Classical.choice, Quot.sound."

#check @LRX.exact_diameter_all
#print axioms LRX.exact_diameter_all
#print axioms LRX.sharp_diameter_all
#print axioms LRX.nonzero_lift_routing
#print axioms LRX.diam_lower

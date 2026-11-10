/- Run in the ORIGINAL development repository (lake env lean <this file>).
Writes the constant dependency closure of LRX.exact_diameter_all (used.tsv) and the list of
all project constants (all.tsv) to the current directory; input of extract_package.py. -/
import LRX.SharpDiameterAll
open Lean Elab Command

partial def collect (env : Environment) (start : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack := start.toList
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        for c in ci.type.getUsedConstants do stack := c :: stack
        if let some v := ci.value? (allowOpaque := true) then
          for c in v.getUsedConstants do stack := c :: stack
        match ci with
        | .inductInfo i => for c in i.ctors do stack := c :: stack
        | .ctorInfo c => stack := c.induct :: stack
        | .recInfo r => for c in r.all do stack := c :: stack
        | _ => pure ()
  return seen

run_cmd do
  let env ← getEnv
  let used := collect env #[`LRX.exact_diameter_all]
  let mut lines : Array String := #[]
  for n in used.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if (`Mathlib).isPrefixOf mod || (`Init).isPrefixOf mod || (`Std).isPrefixOf mod || (`Lean).isPrefixOf mod || (`Batteries).isPrefixOf mod || (`Aesop).isPrefixOf mod || (`Qq).isPrefixOf mod || (`Plausible).isPrefixOf mod then continue
    let ci := env.find? n |>.get!
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "ax" | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"
    lines := lines.push s!"{mod}\t{kind}\t{n}"
  -- totals per module
  let mut tot : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless [`LRX, `Research, `GraphBridge, `Reachability, `GraphLower, `Submission].any (·.isPrefixOf mod) do continue
    let kind := if ci.isTheorem then "thm" else "other"
    tot := tot.push s!"{mod}\t{kind}\t{n}"
  IO.FS.writeFile "used.tsv" (String.intercalate "\n" lines.toList)
  IO.FS.writeFile "all.tsv" (String.intercalate "\n" tot.toList)
  logInfo m!"used {lines.size}, all {tot.size}"

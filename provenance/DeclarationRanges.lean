module

/- Run in the ORIGINAL development repository. Writes declaration ranges (ranges.tsv)
of all project constants; input of extract_package.py. -/
public import LRX.SharpDiameterAll

@[expose] public section
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless [`LRX, `Research, `GraphBridge, `Reachability, `GraphLower, `Submission].any (·.isPrefixOf mod) do continue
    let r ← liftCoreM <| findDeclarationRanges? n
    match r with
    | none => pure ()
    | some r =>
      let simp := (Lean.Meta.simpExtension.getState env).lemmaNames.contains (.decl n)
      let kind := if ci.isTheorem then "thm" else if ci.isDefinition then "def" else "other"
      lines := lines.push s!"{mod}\t{n}\t{kind}\t{r.range.pos.line}\t{r.range.pos.column}\t{r.range.endPos.line}\t{r.range.endPos.column}\t{simp}"
  IO.FS.writeFile "ranges.tsv" (String.intercalate "\n" lines.toList)
  logInfo m!"ranges {lines.size}"

module

public import LRX.FullCycleService
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

@[expose] public section

/-! Canonical cycle extraction eliminates the itinerary witness from the public
service theorem. The constructed word covers a single cycle with full support.
Its X count is raw; this is not yet the sharp diameter upper theorem. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem follows_iff_isChain (p : State n) (path : List (Fin n)) :
    Follows p path ↔ path.IsChain (fun a b => (p⁻¹) a=b) := by
  induction path with
  | nil => simp [Follows]
  | cons a rest ih =>
    cases rest with
    | nil => simp [Follows]
    | cons b rest =>
      change ((p⁻¹) a=b ∧ Follows p (b::rest)) ↔ _
      rw [List.isChain_cons_cons, ih]

end LRX.BufferProgram

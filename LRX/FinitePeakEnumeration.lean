module

public import LRX.PeakProfileLargeCount

@[expose] public section

/-! A computable bounded enumeration of the necessary scalar profiles.
Completeness is proved from the predicate; no square-root pruning is trusted. -/
namespace LRX.FinitePeak

def integerInterval (lo hi : ℤ) : List ℤ :=
  (List.range (hi-lo+1).toNat).map (fun (i : ℕ) => lo+(i : ℤ))

theorem mem_integerInterval (lo hi x : ℤ) : x ∈ integerInterval lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  constructor
  · intro hx
    obtain ⟨i,hi,hx⟩ := List.mem_map.mp hx
    have hb := List.mem_range.mp hi
    rw [← hx]
    omega
  · rintro ⟨hl,hh⟩
    apply List.mem_map.mpr
    refine ⟨(x-lo).toNat,List.mem_range.mpr ?_,?_⟩ <;> omega

end LRX.FinitePeak

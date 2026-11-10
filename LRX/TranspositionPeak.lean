module

public import LRX.PairExactCost
public import LRX.GlobalPeakServiceFamily

@[expose] public section

namespace LRX.FiniteCuts
variable {n : ℕ}

theorem swap_half_load_le_one (a b : Fin n) (hab : a.val < b.val) (e : ℕ) :
    halfLoad (Equiv.swap a b) e ≤ 1 := by
  classical
  have hf : forward (Equiv.swap a b) e ⊆ {a} := by
    intro i hi
    have hh := (mem_forward _ _ _).mp hi
    by_cases hia : i=a
    · simpa only [Finset.mem_singleton] using hia
    · by_cases hib : i=b
      · subst i
        rw [Equiv.swap_apply_right] at hh
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib] at hh
        omega
  simpa only [halfLoad,Finset.card_singleton] using Finset.card_le_card hf

/-- A nontrivial transposition contributes exactly one half-peak. -/
theorem transposition_left_peak [NeZero n] (a b : Fin n) (hab : a ≠ b) :
    leftPeak (Equiv.swap a b) n=1 := by
  have hval : a.val ≠ b.val := fun hh => hab (Fin.ext hh)
  have hcap (e : ℕ) : halfLoad (Equiv.swap a b) e ≤ 1 := by
    rcases lt_or_gt_of_ne hval with h | h
    · exact swap_half_load_le_one a b h e
    · simpa only [Equiv.swap_comm b a] using swap_half_load_le_one b a h e
  have hle : leftPeak (Equiv.swap a b) n ≤ 1 :=
    Finset.sup_le (fun e _ => hcap e)
  have hpos := cycle_global_peak_positive _ (Equiv.Perm.isCycle_swap hab)
  omega

#print axioms transposition_left_peak
end LRX.FiniteCuts

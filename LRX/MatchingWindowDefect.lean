module

public import LRX.CycleDefectMonotonicity

@[expose] public section

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ}

/-- A matching invariant window cannot have more defect than the whole map. -/
theorem matching_window_defect_le (A : FillingWindow n) (p : State n)
    (hm : A.Matches p) : cycleDefect A.filling ≤ cycleDefect p := by
  classical
  let q := permutation A.window A.filling
  let r := q⁻¹*p
  have he : q*r=p := by dsimp only [r]; group
  have hd : q.Disjoint r := by
    intro i
    by_cases hi : Contains A.window i
    · right
      obtain ⟨j,rfl⟩ := (contains_iff A.window i).mp hi
      have hq : q (embed A.window j)=p (embed A.window j) := by
        dsimp only [q]
        rw [permutation_embed,hm j]
      change q.symm (p (embed A.window j))=embed A.window j
      rw [← hq]
      exact q.symm_apply_apply _
    · exact Or.inl (permutation_outside A.window A.filling i hi)
  have h := cycle_defect_disjoint_superadditive q r hd
  have hr := finite_depth_rank r
  have hq : cycleDefect q=cycleDefect A.filling := by
    simp only [q,cycleDefect,displacement_mass,inversion_number_window,
      permutation_support_card,permutation_cycle_count]
  rw [he,hq] at h
  unfold cycleDefect at *
  omega

#print axioms matching_window_defect_le
end LRX.FiniteWindow

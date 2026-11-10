module

public import LRX.WindowFamilyFixedCount

@[expose] public section

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ}

theorem reversal_fixed_count (b : ℕ) :
    b-(Fin.revPerm : State b).support.card=b%2 := by
  classical
  have hcard : (Fin.revPerm : State b).supportᶜ.card=b%2 := by
    by_cases he : b%2=0
    · have hs : (Fin.revPerm : State b).supportᶜ=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hh : Fin.revPerm i=i := by simpa using hi
        have hv := congrArg Fin.val hh
        simp only [Fin.revPerm_apply,Fin.val_rev] at hv
        have := i.isLt
        omega
      simp only [hs,Finset.card_empty,he]
    · let c : Fin b := ⟨b/2,by omega⟩
      have hs : (Fin.revPerm : State b).supportᶜ={c} := by
        ext i
        simp only [Finset.mem_compl,Equiv.Perm.mem_support,not_not,
          Finset.mem_singleton,Fin.ext_iff,Fin.revPerm_apply,Fin.val_rev]
        dsimp only [c]
        have := i.isLt
        omega
      rw [hs,Finset.card_singleton]
      omega
  simpa only [Finset.card_compl,Fintype.card_fin] using hcard

/-- The reversed windows contribute exactly one fixed position per odd
window. The original fillings play no role in this upper-map count. -/
theorem reversed_window_family_fixed_count (As : List (FillingWindow n)) (Q : State n)
    (hrev : ∀ A ∈ As, ∀ i, Q (embed A.window i)=embed A.window (Fin.revPerm i))
    (hd : As.Pairwise FillingWindow.Apart) :
    (familyPositions As \ Q.support).card=(As.map (fun A => A.size%2)).sum := by
  classical
  induction As with
  | nil => simp [familyPositions]
  | cons A As ih =>
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hd
    have hrest := ih (fun B hB => hrev B (List.mem_cons_of_mem _ hB)) hAs
    have hdis : Disjoint (windowPositions A.window) (familyPositions As) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨B,hB,hBi⟩ := (mem_family_positions As i).mp hj
      exact hA B hB i (Finset.mem_filter.mp hi).2 hBi
    have hlocal := matching_window_fixed_count A.window Q Fin.revPerm
      (hrev A (List.mem_cons_self ..))
    rw [reversal_fixed_count] at hlocal
    simp only [familyPositions,Finset.union_sdiff_distrib,
      Finset.card_union_of_disjoint (hdis.mono Finset.sdiff_subset Finset.sdiff_subset),
      hlocal,hrest,List.map_cons,List.sum_cons]

#print axioms reversal_fixed_count
#print axioms reversed_window_family_fixed_count
end LRX.FiniteWindow

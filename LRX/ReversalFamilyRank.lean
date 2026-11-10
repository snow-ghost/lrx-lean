module

public import LRX.ReversalWindowFamily
public import LRX.WindowReplacementRank

@[expose] public section

namespace LRX.FiniteWindow
open FiniteRankOrder
variable {n : ℕ}

/-- Simultaneous reversal of actual pairwise disjoint invariant fillings
raises the original map in finite rank order. -/
theorem below_reverse_windows (As : List (FillingWindow n)) (p : State n)
    (hm : ∀ A ∈ As, A.Matches p) (ha : As.Pairwise FillingWindow.Apart) :
    Below p (reverseWindows As p) := by
  induction As generalizing p with
  | nil => exact below_refl p
  | cons A As ih =>
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp ha
    have hhead := below_reversal_replacement A.window p A.filling (hm A (by simp))
    have htail := ih (A.reverseIn p) (fun B hB =>
      FillingWindow.matches_after_apart A B p (hA B hB) (hm B (by simp [hB]))) hAs
    exact below_trans hhead htail

/-- Every coordinate outside the whole selected family retains its original arrow. -/
theorem reverse_windows_outside (As : List (FillingWindow n)) (p : State n) (i : Fin n)
    (hi : ∀ A ∈ As, ¬Contains A.window i) : reverseWindows As p i=p i := by
  induction As generalizing p with
  | nil => rfl
  | cons A As ih =>
    change reverseWindows As (A.reverseIn p) i=p i
    rw [ih (A.reverseIn p) (fun B hB => hi B (by simp [hB]))]
    exact replace_outside A.window p A.filling Fin.revPerm i (hi A (by simp))

/-- Every selected window is an actual reversal in the final upper map. -/
theorem reverse_windows_on_member (As : List (FillingWindow n)) (p : State n)
    (hm : ∀ A ∈ As, A.Matches p) (ha : As.Pairwise FillingWindow.Apart)
    (A : FillingWindow n) (hA : A ∈ As) (i : Fin A.size) :
    reverseWindows As p (embed A.window i)=embed A.window (Fin.revPerm i) := by
  induction As generalizing p with
  | nil => simp at hA
  | cons B Bs ih =>
    obtain ⟨hB,hBs⟩ := List.pairwise_cons.mp ha
    rcases List.mem_cons.mp hA with hAB | hA
    · subst A
      change reverseWindows Bs (B.reverseIn p) (embed B.window i)=_
      rw [reverse_windows_outside Bs (B.reverseIn p) _ (fun A hA =>
        hB A hA _ (contains_embed B.window i))]
      exact replace_embed B.window p B.filling Fin.revPerm (hm B (by simp)) i
    · exact ih (B.reverseIn p) (fun A hA =>
        FillingWindow.matches_after_apart B A p (hB A hA) (hm A (by simp [hA]))) hBs hA

#print axioms below_reverse_windows
#print axioms reverse_windows_outside
#print axioms reverse_windows_on_member
end LRX.FiniteWindow

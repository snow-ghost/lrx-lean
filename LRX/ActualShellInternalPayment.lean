import LRX.ActualShellWidths
import LRX.ActualShellInternalGeometry

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

theorem prefix_even_internal_actual_shell_paid (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (heven : (prefixSourceCore p).card%2=0)
    (B : FillingWindow n) (hB : B ∈ positiveSourceFamily p (componentSet p 0).card)
    (hdom : n-(prefixSourceCore p).card < 2*B.size) : shellE p ≤ 0 := by
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hb : B.size ∈ shellWidths p := List.mem_append_left _ (List.mem_map.mpr ⟨B,hB,rfl⟩)
  have hprice := prefix_even_shell_member_price p hmaj hm hlarge hz heven B.size hb
  have hH := prefix_even_zero_defect_positive_reserve p hmaj hm hlarge hz heven
  change 1 ≤ shellH p at hH
  have he := prefix_multiple_components_exterior_size p hc hm
  let t : ℤ := 2*(B.size : ℤ)-((n-(prefixSourceCore p).card : ℕ) : ℤ)
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hgeom := prefix_zero_defect_window_internal_deficit p hmaj hm hlarge hz B hB
  dsimp only at hgeom
  rw [heven,Nat.cast_zero,sub_zero,max_eq_right (show 0 ≤ t by omega)] at hgeom
  exact internal_shell_positive_peak_paid (shellE p) (shellH p) t
    ((n-(componentSet p 0).card : ℕ) : ℤ) hH ht (by omega) hprice hgeom

#print axioms prefix_even_internal_actual_shell_paid
end LRX.FiniteCuts

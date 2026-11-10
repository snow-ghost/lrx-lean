module

public import LRX.JoinedExteriorGapWord

@[expose] public section

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

theorem moving_between_outer (p : State n) (hc : (componentRoots p).card=k+1)
    (x : Fin n) (hx : p.symm x ≠ x) :
    (outerLeft p hc).val ≤ x.val ∧ x.val ≤ (outerRight p hc).val := by
  let e := componentOrder p hc
  obtain ⟨a,ha,hax⟩ := component_roots_cover p x hx
  obtain ⟨j,hj⟩ := component_order_surjective p hc a ha
  rw [← hj] at hax
  have hlo := component_left_bound p (e j) x hax
  have hhi := component_right_bound p (e j) x hax
  constructor
  · by_cases hz : j=0
    · simpa only [hz,e,outerLeft] using hlo
    · have hjpos : (0 : Fin (k+1)) < j := by
        change 0 < j.val
        have hh : j.val ≠ 0 := fun h => hz (Fin.ext h)
        omega
      have hh := ordered_component_roots p (component_order_mem p hc 0)
        (component_order_mem p hc j) (e.strictMono hjpos)
      have hb := component_left_bound p (e 0) (componentRight p (e 0)) (component_right_path p (e 0))
      change (componentRight p (e 0)).val < (componentLeft p (e j)).val at hh
      change (componentLeft p (e 0)).val ≤ x.val
      omega
  · by_cases hz : j=Fin.last k
    · simpa only [hz,e,outerRight] using hhi
    · have hjlt : j < Fin.last k := by
        change j.val < k
        have hh : j.val ≠ k := fun h => hz (Fin.ext h)
        have := j.isLt
        omega
      have hh := ordered_component_roots p (component_order_mem p hc j)
        (component_order_mem p hc (Fin.last k)) (e.strictMono hjlt)
      have hb := component_right_bound p (e (Fin.last k)) (componentLeft p (e (Fin.last k)))
        (component_left_path p (e (Fin.last k)))
      change (componentRight p (e j)).val < (componentLeft p (e (Fin.last k))).val at hh
      change x.val ≤ (componentRight p (e (Fin.last k))).val
      omega

#print axioms moving_between_outer
end LRX.FiniteCuts

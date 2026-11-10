import LRX.FiniteCycleAvailability
import LRX.ReflectedExactService

/-! Both finite peak discounts are attained by services with exact integer endpoints. -/
namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {b : ℕ} [NeZero b]

theorem left_peak_exact_service (hb : 2 ≤ b) (p : State b) (hp : p.IsCycle)
    (y : ℕ) (hy : y ≤ b) (hpos : 0 < leftPeak p y) :
    ∃ a : ExactService b, a.service.port.val+1 ≤ y ∧ a.service.target=p⁻¹ ∧
      a.displacement=displacement p ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)-2*(leftPeak p y : ℤ) := by
  obtain ⟨i, hi, hiy, hload⟩ := left_peak_port p y hy hpos
  obtain ⟨s, hs, ht, hx, hl⟩ := single_cycle_exact_service (p := p⁻¹) hb hp.inv
    (canonical_lift p) (displacement_short p) i (displacement_ne_of_moved p i hi)
  rw [port_load_eq_twice_half, hload] at hl
  refine ⟨s, ?_, ht, hx, ?_⟩
  · rw [hs]; exact hiy
  · exact hl

#print axioms left_peak_exact_service
end LRX.FiniteCuts

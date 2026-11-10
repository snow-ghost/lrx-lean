import LRX.CanonicalServiceFamily
import LRX.FiniteCycleScan
import LRX.FiniteDisplacementSum
import LRX.FiniteExactAvailability
import LRX.OrderedExactRoute
import LRX.PacketWindowRoutes
import LRX.PrunedLoad
import LRX.RootChildrenAssembly
import LRX.WindowCycleSelection
import LRX.WindowFamilyBridge

/-! In a window no wider than half the circle, a strictly short lift has the
canonical finite displacements. The no-winding premise is derived here. -/
namespace LRX.FiniteWindow
variable {n b : ℕ} [NeZero n]

omit [NeZero n] in
theorem narrow_window_displacement {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (W : Window n b) (hwidth : 2*b ≤ n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i)) (i : Fin b) :
    d (embed W i)=FiniteCuts.displacement filling i := by
  have hm : Int.ModEq (n : ℤ) (d (embed W i)) (FiniteCuts.displacement filling i) := by
    have h := (hd.2 (embed W i)).sub_right (embed W i : ℤ)
    rw [hmatch] at h
    simpa [FiniteCuts.displacement,embed] using h
  have hm' : Int.ModEq (n : ℤ) (d (embed W i)-FiniteCuts.displacement filling i) 0 := by
    simpa using hm.sub_right (FiniteCuts.displacement filling i)
  have hc := FiniteCuts.displacement_short filling i
  have hs := hshort (embed W i)
  have ht := abs_sub (d (embed W i)) (FiniteCuts.displacement filling i)
  have hbound : |d (embed W i)-FiniteCuts.displacement filling i| < (n : ℤ) := by omega
  have hz : d (embed W i)-FiniteCuts.displacement filling i=0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.modEq_zero_iff_dvd.mp hm')
    have hcast : ((d (embed W i)-FiniteCuts.displacement filling i).natAbs : ℤ) <
        ((n : ℤ).natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs,abs_of_nonneg (show (0 : ℤ) ≤ n by positivity)] using hbound
    exact_mod_cast hcast
  exact sub_eq_zero.mp hz

omit [NeZero n] in
theorem majorized_short {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (i : Fin n) :
    2*|d i| < (n : ℤ) := by
  have h := AffineLift.short_coordinates hd.1 hm i
  by_cases hi : 0 ≤ d i
  · rw [abs_of_nonneg hi]; omega
  · rw [abs_of_neg (by omega : d i < 0)]; omega

open scoped BigOperators

#print axioms narrow_window_displacement
end LRX.FiniteWindow

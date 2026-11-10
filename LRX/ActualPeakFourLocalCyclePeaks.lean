import LRX.PeakFourSourceRigidity
import LRX.WindowCyclePeakFamily
import LRX.FillingPeakRecenter

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem filling_cycle_peak_one_recenter (p : State n) (root : Fin n)
    (hpeak : ∀ c ∈ fillingCycles p, leftPeak c n=1) :
    ∀ c ∈ fillingCycles (localTarget p 0 (componentLeft p root)), leftPeak c n=1 := by
  classical
  let r := componentLeft p root
  have hcan := component_cut_canonical_displacement p root
  intro d hd
  let c := rotation r*d*(rotation r)⁻¹
  have he : localTarget c 0 r=d := by simp [c,local_target_zero,mul_assoc]
  have hc : c ∈ fillingCycles p := (filling_cycle_recenter_iff p c r hcan).mp (by rwa [he])
  have hp := cycle_peak_recenter p c r hcan (Finset.mem_filter.mp hc).1
  rw [he,hpeak c hc] at hp
  exact hp

/-- The peak-one condition of actual filling cycles descends to every
local cycle of a matched window disjoint from the source packets. -/
theorem matched_filling_window_cycle_peak_one (p : State n) (A : FillingWindow n)
    (hm : A.Matches p.symm) (ha : ∀ i ∈ sourcePackets p, ¬Contains A.window i)
    (hpeak : ∀ c ∈ fillingCycles p, leftPeak c n=1)
    (c : State A.size) (hc : c ∈ A.filling.cycleFactorsFinset) : leftPeak c A.size=1 := by
  classical
  have hmem : permutation A.window c ∈ A.embeddedCycles :=
    List.mem_map.mpr ⟨c,Finset.mem_toList.mpr hc,rfl⟩
  have hamb := matched_window_cycle_mem_fillings p A hm ha _ hmem
  have hup := peak_le_embedded_peak A.window c
  rw [hpeak _ hamb] at hup
  obtain ⟨i,hi⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
  letI : NeZero A.size := ⟨by have := i.isLt; omega⟩
  have hpos := moved_global_peak_positive c i (Equiv.Perm.mem_support.mp hi)
  omega

theorem actual_peak_four_local_cycle_peak_one (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : sourceHalfPeak p=4)
    (A : FillingWindow n)
    (hA : A ∈ positiveSourceFamily (localTarget p 0 (componentLeft p root))
      (componentSet p root).card)
    (c : State A.size) (hcA : c ∈ A.filling.cycleFactorsFinset) : leftPeak c A.size=1 := by
  obtain ⟨_,_,_,_,_,hS,_⟩ := peak_four_source_rigidity hn p hmaj hmax hc hk root hlarge ht hpos he hp hv hU
  have hpeak := filling_cycles_peak_one_of_equality p hS
  have hqpeak := filling_cycle_peak_one_recenter p root hpeak
  have hspec := positive_source_family_spec (localTarget p 0 (componentLeft p root))
    (componentSet p root).card
  exact matched_filling_window_cycle_peak_one _ A (hspec.1 A hA)
    (positive_family_avoids_source _ _ A hA) hqpeak c hcA

#print axioms filling_cycle_peak_one_recenter
#print axioms matched_filling_window_cycle_peak_one
#print axioms actual_peak_four_local_cycle_peak_one
end LRX.FiniteCuts

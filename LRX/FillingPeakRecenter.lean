import LRX.ComponentCutPeakInvariant

/-! M4: filling-cycle peak sums survive a canonical zero-cut recentering.
This is separate from preservation of the global source peak. -/
namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem recentered_cycle_support (c : State n) (r i : Fin n) :
    i ∈ (localTarget c 0 r).support ↔ rotation r i ∈ c.support := by
  simp only [Equiv.Perm.mem_support,local_target_zero,Equiv.Perm.mul_apply]
  change (rotation r).symm (c (rotation r i)) ≠ i ↔ _
  constructor
  · intro h he
    apply h
    rw [he,Equiv.symm_apply_apply]
  · intro h he
    apply h
    have hh := congrArg (rotation r) he
    simpa only [Equiv.apply_symm_apply] using hh

theorem recentered_cycle_factor_iff (p c : State n) (r : Fin n) :
    localTarget c 0 r ∈ ((localTarget p 0 r)⁻¹).cycleFactorsFinset ↔
      c ∈ (p⁻¹).cycleFactorsFinset := by
  rw [local_target_zero c,local_inverse_conjugate]
  simpa only [inv_inv] using Equiv.Perm.mem_cycleFactorsFinset_conj p⁻¹ (rotation r)⁻¹ c

theorem filling_cycle_recenter_iff (p c : State n) (r : Fin n)
    (hcan : localDisplacement (displacement p.symm) r=displacement (localTarget p 0 r).symm) :
    localTarget c 0 r ∈ fillingCycles (localTarget p 0 r) ↔ c ∈ fillingCycles p := by
  classical
  simp only [fillingCycles,Finset.mem_filter,recentered_cycle_factor_iff]
  apply and_congr_right
  intro _
  constructor
  · intro hd
    apply Finset.disjoint_left.mpr
    intro j hj hs
    obtain ⟨i,rfl⟩ := (rotation r).surjective j
    exact Finset.disjoint_left.mp hd ((recentered_cycle_support c r i).mpr hj)
      ((source_packets_recenter p r hcan i).mpr hs)
  · intro hd
    apply Finset.disjoint_left.mpr
    intro i hi hs
    exact Finset.disjoint_left.mp hd ((recentered_cycle_support c r i).mp hi)
      ((source_packets_recenter p r hcan i).mp hs)

/-- Canonical displacement transfer of the full map restricts to each real cycle. -/
theorem cycle_displacement_recenter (p c : State n) (r : Fin n)
    (hcan : localDisplacement (displacement p.symm) r=displacement (localTarget p 0 r).symm)
    (hc : c ∈ (p⁻¹).cycleFactorsFinset) :
    displacement (localTarget c 0 r)=localDisplacement (displacement c) r := by
  classical
  have hact := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2
  funext i
  by_cases hi : rotation r i ∈ c.support
  · have he : (localTarget c 0 r) i=(localTarget p 0 r).symm i := by
      change (localTarget c 0 r) i=(localTarget p 0 r)⁻¹ i
      rw [local_target_zero c,local_inverse_conjugate]
      change (rotation r).symm (c (rotation r i))=(rotation r).symm (p⁻¹ (rotation r i))
      rw [hact _ hi]
    have hd := congrFun hcan i
    change displacement p.symm (rotation r i)=displacement (localTarget p 0 r).symm i at hd
    change displacement (localTarget c 0 r) i=displacement c (rotation r i)
    unfold displacement at hd ⊢
    rw [he,hact _ hi]
    exact hd.symm
  · have hcfix : c (rotation r i)=rotation r i := Equiv.Perm.notMem_support.mp hi
    have hfix : (localTarget c 0 r) i=i := by
      rw [local_target_zero]
      change (rotation r).symm (c (rotation r i))=i
      rw [hcfix,Equiv.symm_apply_apply]
    change displacement (localTarget c 0 r) i=displacement c (rotation r i)
    simp only [displacement,hfix,hcfix,sub_self]

theorem cycle_peak_recenter (p c : State n) (r : Fin n)
    (hcan : localDisplacement (displacement p.symm) r=displacement (localTarget p 0 r).symm)
    (hc : c ∈ (p⁻¹).cycleFactorsFinset) : leftPeak (localTarget c 0 r) n=leftPeak c n := by
  apply left_peak_eq_of_recentered_load c (localTarget c 0 r) r
  intro i
  rw [cycle_displacement_recenter p c r hcan hc,port_load_recenter]

/-- Exact filling sum invariance, through a bijection of the actual cycles. -/
theorem filling_half_peak_sum_recenter (p : State n) (r : Fin n)
    (hcan : localDisplacement (displacement p.symm) r=displacement (localTarget p 0 r).symm) :
    fillingHalfPeakSum (localTarget p 0 r)=fillingHalfPeakSum p := by
  classical
  have hsum (q : State n) : fillingHalfPeakSum q=∑ c ∈ fillingCycles q, (leftPeak c n : ℤ) := by
    symm
    simpa only [fillingHalfPeakSum,Finset.toList_toFinset] using
      List.sum_toFinset (fun c : State n => (leftPeak c n : ℤ)) (Finset.nodup_toList (fillingCycles q))
  rw [hsum,hsum]
  symm
  apply Finset.sum_bij (fun c _ => localTarget c 0 r)
  · intro c hc
    exact (filling_cycle_recenter_iff p c r hcan).mpr hc
  · intro c hc d hd he
    simp only [local_target_zero] at he
    exact mul_left_cancel (mul_right_cancel he)
  · intro d hd
    let c := rotation r*d*(rotation r)⁻¹
    have he : localTarget c 0 r=d := by simp [c,local_target_zero,mul_assoc]
    refine ⟨c,?_,he⟩
    apply (filling_cycle_recenter_iff p c r hcan).mp
    rwa [he]
  · intro c hc
    rw [cycle_peak_recenter p c r hcan (Finset.mem_filter.mp hc).1]

theorem component_cut_filling_half_peak_sum (p : State n) (root : Fin n) :
    fillingHalfPeakSum (localTarget p 0 (componentLeft p root))=fillingHalfPeakSum p :=
  filling_half_peak_sum_recenter p _ (component_cut_canonical_displacement p root)

#print axioms filling_half_peak_sum_recenter
#print axioms component_cut_filling_half_peak_sum
end LRX.FiniteCuts

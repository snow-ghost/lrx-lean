module

public import LRX.FillingPeakRecenter
public import LRX.SourcePacketCyclePartition

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

theorem filling_cycle_count_recenter (p : State n) (r : Fin n)
    (hcan : localDisplacement (displacement p.symm) r=displacement (localTarget p 0 r).symm) :
    (fillingCycles (localTarget p 0 r)).card=(fillingCycles p).card := by
  classical
  symm
  apply Finset.card_bij (fun c _ => localTarget c 0 r)
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

theorem cycle_factor_count_recenter (p : State n) (r : Fin n) :
    (localTarget p 0 r).cycleFactorsFinset.card=p.cycleFactorsFinset.card := by
  rw [local_target_zero]
  have hh := congrArg Multiset.card
    (Equiv.Perm.cycleType_conj (σ := p) (τ := (rotation r)⁻¹))
  simpa only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card_val,inv_inv] using hh

#print axioms filling_cycle_count_recenter
#print axioms cycle_factor_count_recenter
end LRX.FiniteCuts

module

public import LRX.TwoVertexCoreFixedCount

@[expose] public section

/-! The covered packet has enough remaining budget to pay every fixed
position once n >= 7; the two-vertex exceptional case is excluded by gaps. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem core_fixed_budget_inequality {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) :
    (fixedCount p : ℤ)^2-3*(fixedCount p : ℤ)+((PrunedLift.core p d 0).card : ℤ)-2 ≤
      2*(exchangeReserve d+epsilon d-(fixedCount p : ℤ)) := by
  have hi := ZeroGap.activity_core_inversion_bound hd (FiniteWindow.majorized_short hd hm) 0
  have he := fixed_energy_deficit hd hm
  have hf := fixed_count_identity p
  have hn : (n : ℤ)=2*(n/2 : ℕ)+(n%2 : ℕ) := by omega
  unfold exchangeReserve epsilon at *
  nlinarith

theorem packet_fixed_budget (hn : 7 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) :
    (fixedCount p : ℤ) ≤ exchangeReserve d+epsilon d := by
  have hshort : |d 0| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm 0
    have := abs_nonneg (d 0)
    omega
  have hmov : p⁻¹ 0 ≠ 0 := fun h => hroot (BufferProgram.fixed_short_displacement hd 0 hshort h)
  have hcore := moving_core_card_ge_two (d := d) hmov
  have hbound := core_fixed_budget_inequality hd hm
  by_cases hz : fixedCount p=0
  · rw [hz,Nat.cast_zero]
    exact add_nonneg (ZeroGap.exchange_reserve_nonneg hd hm) (epsilon_nonneg hd hm)
  by_cases hf : 3 ≤ fixedCount p
  · have hf' : (3 : ℤ) ≤ fixedCount p := by exact_mod_cast hf
    have hc' : (2 : ℤ) ≤ (PrunedLift.core p d 0).card := by exact_mod_cast hcore
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ fixedCount p by positivity) (show (0 : ℤ) ≤ (fixedCount p : ℤ)-3 by omega)]
  · have hc3 : 3 ≤ (PrunedLift.core p d 0).card := by
      by_contra hc
      have hc2 : (PrunedLift.core p d 0).card=2 := by omega
      have := two_vertex_core_fixed_count hn hd hm hcover hmov hc2
      omega
    have hcases : fixedCount p=1 ∨ fixedCount p=2 := by omega
    rcases hcases with h | h <;> rw [h] at hbound <;> norm_num at hbound <;> omega

theorem fixed_gap_sharp_budget (hn : 7 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (a : Fin n)
    (hz : ∀ i ∈ positions (PrunedLift.core p d 0) a, d i=0) :
    (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
      (∑ i : Fin n, |d i|)+(size (PrunedLift.core p d 0) a : ℤ) ≤ (n.choose 2 : ℤ) := by
  have hf := packet_fixed_budget hn hd hm hroot hcover
  have hs := fixed_gap_size_le hd a hz
  have hN := quarter_budget (n := n) (NeZero.pos n)
  unfold exchangeReserve epsilon at hf
  omega

#print axioms core_fixed_budget_inequality
#print axioms packet_fixed_budget
#print axioms fixed_gap_sharp_budget
end LRX.FiniteGaps

module

public import LRX.ActualShellPrice
public import LRX.PrefixCoreEnergy

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The packet's own peak bounds its mass on its actual component width,
not on the size of the whole ambient circle. -/
theorem prefix_packet_peak_energy (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (U : ℕ) (hpeak : leftPeak ((canonicalRootPacket p 0)⁻¹) n ≤ U)
    (hwidth : 2*U ≤ (componentSet p 0).card) :
    (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) ≤
      2*(U : ℤ)*(((componentSet p 0).card : ℤ)-U) := by
  classical
  let L := (componentSet p 0).card
  let A := (canonicalRootPacket p 0)⁻¹
  let W : Window n L := ⟨0,by simpa only [Nat.zero_add,Fintype.card_fin] using
    (Finset.card_le_univ (componentSet p 0))⟩
  have hW (i : Fin n) : Contains W i ↔ i.val < L := by simp [Contains,W]
  have hs : A.support=prefixSourceCore p := by
    dsimp only [A]
    rw [Equiv.Perm.support_inv,prefix_root_packet_support p hm hc]
  have hclosed (i : Fin n) (hi : Contains W i) : Contains W (A i) := by
    by_cases hmove : i ∈ A.support
    · have him := Equiv.Perm.apply_mem_support.mpr hmove
      rw [hs] at him
      exact (hW _).mpr (Finset.mem_filter.mp him).2
    · have hfix : A i=i := Equiv.Perm.notMem_support.mp hmove
      rwa [hfix]
  obtain ⟨f,hf⟩ := exists_restriction_of_inverse_closed W A.symm (by
    intro i hi
    simpa only [Equiv.symm_symm] using hclosed i hi)
  have hfp : leftPeak f L ≤ U :=
    (prefix_window_peak_le W rfl A f (by simpa only [Equiv.symm_symm] using hf)).trans hpeak
  have henergy := finite_energy_peak_upper f U hfp hwidth
  have hmass := prefix_root_packet_mass p hm hc
  have htotal : (∑ i, |displacement A i|)=∑ i ∈ windowPositions W, |displacement A i| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hout : ¬ Contains W i := by simpa only [windowPositions,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    have hfix : A i=i := Equiv.Perm.notMem_support.mp (by
      intro hh
      rw [hs] at hh
      exact hout ((hW i).mpr (Finset.mem_filter.mp hh).2))
    simp [displacement,hfix]
  have hlocal : (∑ i ∈ windowPositions W, |displacement A i|)=∑ i, |displacement f i| := by
    rw [sum_window_positions]
    simp_rw [matching_window_displacement W A f (by simpa only [Equiv.symm_symm] using hf)]
  change (∑ i, |displacement A i|)=_ at hmass
  rw [← hmass,htotal,hlocal]
  exact henergy

#print axioms prefix_packet_peak_energy
end LRX.FiniteCuts

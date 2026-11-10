import LRX.JoinedSourceCore

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

theorem source_packets_invariant (p : State n) (i : Fin n) :
    p i ∈ sourcePackets p ↔ i ∈ sourcePackets p := by
  have hc : (p⁻¹).SameCycle (p i) i := by
    simpa using (Equiv.Perm.SameCycle.refl (p⁻¹) (p i)).apply_right
  exact ⟨fun hi => source_packets_predecessor_closed p i (p i) (Or.inl hc.symm) hi,
    fun hi => source_packets_predecessor_closed p (p i) i (Or.inl hc) hi⟩

theorem joined_inverse_outside_packets (p : State n) (hc : (componentRoots p).card=k+1)
    (i : Fin n) (hi : i ∉ sourcePackets p) : (joinedComponents p hc).symm i=p.symm i := by
  apply bridge_sequence_inverse_outside p _ i
  intro uv huv
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp huv
  have he := bridge_endpoints_in_source_packets p hc a
  exact ⟨fun h => hi (h ▸ he.1),fun h => hi (h ▸ he.2)⟩

end LRX.FiniteCuts

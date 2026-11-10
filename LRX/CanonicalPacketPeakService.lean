module

public import LRX.ExtractedPacketDefect
public import LRX.FiniteReachableExactService
public import LRX.FinitePeakPorts

@[expose] public section

/-! M4: a real extracted strong packet has one exact service at its full
peak, without an IsCycle assumption or supplied service-reachability. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Strong reachability is inherited by the actual extracted packet. -/
theorem canonical_packet_support_in_core (p : State n) (root : Fin n)
    (i : Fin n) (hi : i ∈ (canonicalRootPacket p root).support) :
    PrunedLift.InCore (canonicalRootPacket p root)
      (displacement (canonicalRootPacket p root).symm) root i := by
  classical
  let d := displacement p.symm
  let S := PrunedLift.core p d root
  let hS := PrunedLift.core_invariant p d root
  let q := canonicalRootPacket p root
  have hkeep : PrunedLift.KeepsCore p d root S := fun j hj hk =>
    (PrunedLift.mem_core p d root j).mpr ⟨hj,hk⟩
  have hdisp : displacement q.symm = PrunedLift.displacement S d := by
    funext j
    by_cases hj : j ∈ S <;>
      simp [q,canonicalRootPacket,displacement,PrunedLift.displacement,
        PrunedLift.permutation_symm_apply,S,d,hj]
  have hiS : i ∈ S := by
    by_contra hh
    have he : q i=i := by
      change PrunedLift.permutation p S hS i=i
      simp only [PrunedLift.permutation_apply,ite_eq_right hh]
    exact (Equiv.Perm.mem_support.mp hi) he
  have hc := (PrunedLift.mem_core p d root i).mp hiS
  change PrunedLift.InCore q (displacement q.symm) root i
  rw [hdisp]
  exact ⟨PrunedLift.retain_core_path p d root S hS hkeep root
      Relation.ReflTransGen.refl hc.1 hc.2,
    PrunedLift.retain_core_path p d root S hS hkeep i hc.1 hc.2
      Relation.ReflTransGen.refl⟩

/-- One service for the entire (possibly multicycle) packet, with exact
canonical displacement and the full global peak discount. -/
theorem canonical_packet_peak_exact_service (hn : 2 ≤ n) (p : State n)
    (root : Fin n) (hpos : 0 < leftPeak (canonicalRootPacket p root).symm n) :
    ∃ a : ExactService n,
      a.service.target=canonicalRootPacket p root ∧
      a.displacement=displacement (canonicalRootPacket p root).symm ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i, |displacement (canonicalRootPacket p root).symm i|)-
          2*(leftPeak (canonicalRootPacket p root).symm n : ℤ) := by
  let q := canonicalRootPacket p root
  obtain ⟨r,hr,_,hload⟩ := left_peak_port q.symm n le_rfl hpos
  have hrc := canonical_packet_support_in_core p root r
    (by rw [← Equiv.Perm.support_inv q, Equiv.Perm.mem_support]; exact hr)
  have hreach (i : Fin n) (hi : q.symm i ≠ i) : FiniteReach q r i := by
    have hic := canonical_packet_support_in_core p root i
      (by rw [← Equiv.Perm.support_inv q, Equiv.Perm.mem_support]; exact hi)
    exact hrc.2.trans hic.1
  obtain ⟨a,_,ht,hd,hprice⟩ := finite_reachable_exact_service hn q r hr hreach
  rw [port_load_eq_twice_half,hload] at hprice
  exact ⟨a,ht,hd,hprice⟩

#print axioms canonical_packet_support_in_core
#print axioms canonical_packet_peak_exact_service
end LRX.FiniteCuts

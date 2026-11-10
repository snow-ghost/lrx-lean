module

public import LRX.ConnectedEventDefect
public import LRX.PacketCoreBalance

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

noncomputable def canonicalRootPacket (p : State n) (root : Fin n) : State n :=
  PrunedLift.permutation p (PrunedLift.core p (displacement p.symm) root)
    (PrunedLift.core_invariant p (displacement p.symm) root)

/-- D2 for the actual strong core extracted from an original canonical map.
Core closure, inherited shortness and strong connectivity are derived internally. -/
theorem extracted_packet_strong_defect (p : State n)
    (hshort : ∀ i, 2*|displacement p.symm i| < (n : ℤ)) (root : Fin n)
    (hroot : root ∈ p.support) :
    let q := canonicalRootPacket p root
    2*((q.cycleFactorsFinset.card : ℤ)-1) ≤
      (∑ i, |displacement q.symm i|)-
        (LiftedModel.inversionCount (fun i : Fin n => (q.symm i : ℤ)) : ℤ)-
        (q.support.card : ℤ)+(q.cycleFactorsFinset.card : ℤ) := by
  classical
  let d := displacement p.symm
  let S := PrunedLift.core p d root
  let hS := PrunedLift.core_invariant p d root
  let q := canonicalRootPacket p root
  have hkeep : PrunedLift.KeepsCore p d root S := fun i hi hj =>
    (PrunedLift.mem_core p d root i).mpr ⟨hi,hj⟩
  have hrS : root ∈ S := hkeep root Relation.ReflTransGen.refl Relation.ReflTransGen.refl
  have hdisp : displacement q.symm = PrunedLift.displacement S d := by
    funext i
    by_cases hi : i ∈ S <;>
      simp [q,canonicalRootPacket,displacement,PrunedLift.displacement,
        PrunedLift.permutation_symm_apply,S,d,hi]
  have hqs : ∀ i, 2*|displacement q.symm i| < (n : ℤ) := by
    intro i
    rw [hdisp]
    by_cases hi : i ∈ S
    · simpa only [PrunedLift.displacement,if_pos hi] using hshort i
    · simp only [PrunedLift.displacement,if_neg hi,abs_zero,mul_zero]
      exact_mod_cast NeZero.pos n
  have hqr : root ∈ q.support := by
    apply Equiv.Perm.mem_support.mpr
    have he : q root=p root := by
      change PrunedLift.permutation p S hS root=p root
      simp only [PrunedLift.permutation_apply,if_pos hrS]
    rw [he]
    exact Equiv.Perm.mem_support.mp hroot
  have hpacket (i : Fin n) (hi : i ∈ q.support) :
      PrunedLift.InCore q (displacement q.symm) root i := by
    have hiS : i ∈ S := by
      by_contra hh
      have he : q i=i := by
        change PrunedLift.permutation p S hS i=i
        simp only [PrunedLift.permutation_apply,if_neg hh]
      exact (Equiv.Perm.mem_support.mp hi) he
    have hc := (PrunedLift.mem_core p d root i).mp hiS
    rw [hdisp]
    exact ⟨PrunedLift.retain_core_path p d root S hS hkeep root Relation.ReflTransGen.refl hc.1 hc.2,
      PrunedLift.retain_core_path p d root S hS hkeep i hc.1 hc.2 Relation.ReflTransGen.refl⟩
  exact ZeroGap.canonical_packet_strong_defect q hqs root hqr hpacket

#print axioms extracted_packet_strong_defect
end LRX.FiniteCuts

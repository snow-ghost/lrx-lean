module

public import LRX.PrefixRootPacketSupport
public import LRX.ShallowGeometricDeficit

@[expose] public section

namespace LRX.FiniteCuts
open ContractionBlocks.System
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Physical rank model for the actual large initial zero-defect packet.
Its original arrows, exact support size, endpoints, energy and width are derived. -/
theorem prefix_zero_defect_physical_model (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0) :
    ∃ (r : ℕ) (P : State (r+1)) (emb : Fin (r+1) ↪o Fin n),
      P.IsCycle ∧ Shallow P ∧ P.support=Finset.univ ∧
      r+1=(prefixSourceCore p).card ∧
      (∀ i, displacement p.symm (emb i)=(emb (P i) : ℤ)-(emb i : ℤ)) ∧
      StrictMono (fun i => (emb i : ℤ)) ∧
      emb 0=0 ∧ emb (Fin.last r)=componentRight p 0 ∧
      (n : ℤ) ≤ 2*((emb (Fin.last r) : ℤ)-(emb 0 : ℤ)) ∧
      physicalMass P (fun i => (emb i : ℤ))=
        ∑ i ∈ prefixSourceCore p, |displacement p.symm i| ∧
      (∀ i, i ∈ prefixSourceCore p ↔ ∃ j, emb j=i) := by
  classical
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hends := prefix_root_packet_extremes p hm hc
  let q := canonicalRootPacket p 0
  have hsupport : q.support=prefixSourceCore p := prefix_root_packet_support p hm hc
  have hcore := prefix_root_core_eq p hm hc
  have hr : (0 : Fin n) ∈ p.support := by
    have hh : (0 : Fin n) ∈ prefixSourceCore p := by rw [← hsupport]; exact hends.1
    exact (mem_support_inverse p 0).mpr ((mem_source_packets p 0).mp (Finset.mem_filter.mp hh).1).1
  obtain ⟨hcycle,hshallow⟩ := canonical_root_packet_shallow_of_zero_defect p hmaj 0 hr hz
  have hqi : (Equiv.Perm.support q.symm)=q.support := Equiv.Perm.support_inv q
  have hIq : inversionNumber q.symm=inversionNumber q := inversion_number_inverse q
  have hshinv : Shallow q.symm := by
    apply (shallow_iff_direct q.symm).mpr
    rw [displacement_mass_inverse,hIq,hqi]
    exact (shallow_iff_direct q).mp hshallow
  have hcyinv : Equiv.Perm.IsCycle q.symm := Equiv.Perm.isCycle_inv.mpr hcycle
  obtain ⟨m,P,emb,hP,hsh,hfull,hcard,hcomm,himage⟩ := shallow_rank_compression hcyinv hshinv
  rw [hqi,hsupport] at hcard himage
  have hm2 : 2 ≤ m := by
    have hh := hcyinv.two_le_card_support
    rw [hqi,hsupport] at hh
    omega
  cases m with
  | zero => omega
  | succ r =>
    have hmem (i : Fin (r+1)) : emb i ∈ prefixSourceCore p := (himage _).mpr ⟨i,rfl⟩
    have hmatch (i : Fin (r+1)) : q.symm (emb i)=p.symm (emb i) := by
      have hi : emb i ∈ PrunedLift.core p (displacement p.symm) 0 := by rw [hcore]; exact hmem i
      change (PrunedLift.permutation p _ (PrunedLift.core_invariant p (displacement p.symm) 0)).symm (emb i)=_
      simp only [PrunedLift.permutation_symm_apply,if_pos hi]
    have hδ (i : Fin (r+1)) : displacement p.symm (emb i)=(emb (P i) : ℤ)-(emb i : ℤ) := by
      unfold displacement
      rw [← hmatch i,← hcomm i]
    have hmono : StrictMono (fun i => (emb i : ℤ)) := by
      intro i j hij
      have hh := emb.strictMono hij
      change (emb i).val < (emb j).val at hh
      change (emb i : ℤ) < (emb j : ℤ)
      exact_mod_cast hh
    have h0core : (0 : Fin n) ∈ prefixSourceCore p := by rw [← hsupport]; exact hends.1
    have hRcore : componentRight p 0 ∈ prefixSourceCore p := by rw [← hsupport]; exact hends.2.1
    obtain ⟨j,hj⟩ := (himage _).mp h0core
    have he0 : emb 0=0 := by
      have hh := emb.monotone (show (0 : Fin (r+1)) ≤ j from Fin.zero_le _)
      rw [hj] at hh
      exact le_antisymm hh (Fin.zero_le _)
    obtain ⟨k,hk⟩ := (himage _).mp hRcore
    have heR : emb (Fin.last r)=componentRight p 0 := by
      have hh := emb.monotone (Fin.le_last k)
      rw [hk] at hh
      have hbound := (Finset.mem_filter.mp (hmem (Fin.last r))).2
      apply Fin.ext
      have hw := hends.2.2
      change (componentRight p 0).val ≤ (emb (Fin.last r)).val at hh
      omega
    have hwide : (n : ℤ) ≤ 2*((emb (Fin.last r) : ℤ)-(emb 0 : ℤ)) := by
      rw [he0,heR]
      have hw := hends.2.2
      norm_num only [Fin.val_zero,Nat.cast_zero,sub_zero]
      omega
    have hmass : physicalMass P (fun i => (emb i : ℤ))=
        ∑ i ∈ prefixSourceCore p, |displacement p.symm i| := by
      have hset : prefixSourceCore p=Finset.univ.image emb := by
        ext i
        simp only [Finset.mem_image,Finset.mem_univ,true_and,himage]
      rw [hset,Finset.sum_image (fun i _ j _ hij => emb.injective hij)]
      simp only [hδ,physicalMass]
    exact ⟨r,P,emb,hP,hsh,hfull,hcard,hδ,hmono,he0,heR,hwide,hmass,himage⟩

#print axioms prefix_zero_defect_physical_model
end LRX.FiniteCuts

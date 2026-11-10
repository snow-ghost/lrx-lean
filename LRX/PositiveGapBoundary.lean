module

public import LRX.PartitionGapSharpWord
public import LRX.InternalGapLoad

@[expose] public section

/-! A positive load at a packet gap boundary supplies an actual packet arrow
through the gap. This derives the internal-gap premise from physical load. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem positive_load_crossing (d : Fin n → ℤ) (r : Fin n)
    (hpos : 0 < RotationWords.portLoad d r) :
    ∃ i : Fin n, d i ≠ 0 ∧ ∃ k : ℤ,
      min (i : ℤ) ((i : ℤ)+d i) ≤ (r : ℤ)+k*(n : ℤ) ∧
      (r : ℤ)+k*(n : ℤ)+1 ≤ max (i : ℤ) ((i : ℤ)+d i) := by
  classical
  rw [RotationWords.port_load_original] at hpos
  have hw : ∃ i : Fin n, 0 < PeriodicBuffer.edgePassages (n : ℤ)
      ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i) := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    omega
  obtain ⟨i,hi⟩ := hw
  have hdi : d i ≠ 0 := by intro hz; simp [PeriodicBuffer.edgePassages,hz] at hi
  obtain ⟨k,hlo,hhi⟩ := passage_interval (show (0 : ℤ) < n by exact_mod_cast NeZero.pos n) hi
  exact ⟨i,hdi,k,by omega,by omega⟩
end LRX.CycleFootprint

namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem positive_boundary_internal {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (a : Fin n) (ha : a ∈ PrunedLift.core p d 0)
    (hpos : 0 < portLoad d a) : size (PrunedLift.core p d 0) a=0 ∨ Internal p d a := by
  by_cases hz : size (PrunedLift.core p d 0) a=0
  · exact Or.inl hz
  right
  let S := PrunedLift.core p d 0
  have hnext := next_le S a
  have hwidth : a.val+1 < next S a := by change next S a-a.val-1 ≠ 0 at hz; omega
  let x : Fin n := ⟨a.val+1,by omega⟩
  obtain ⟨i,hdi,k,hlo,hhi⟩ := CycleFootprint.positive_load_crossing d a hpos
  have hca := (PrunedLift.mem_core p d 0 a).mp ha
  have hshort : |d 0| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm 0
    have := abs_nonneg (d 0)
    omega
  have hmov0 : p⁻¹ 0 ≠ 0 := fun h => hroot (BufferProgram.fixed_short_displacement hd 0 hshort h)
  have hmova := PrunedLift.moving_reachable p d hmov0 hca.1
  have hed : BufferProgram.ServiceEdge p d i a := Or.inr ⟨hmova,k,hlo,by omega⟩
  have hci : PrunedLift.InCore p d 0 i :=
    ⟨PrunedLift.packet_cover_reaches p d 0 hcover i hdi,
      (Relation.ReflTransGen.single hed).trans hca.2⟩
  refine ⟨i,x,(PrunedLift.mem_core p d 0 i).mpr hci,?_,k,?_,?_⟩
  · apply (mem_positions S a x).mpr
    exact ⟨by dsimp [x]; omega,hwidth⟩
  · change min (i : ℤ) ((i : ℤ)+d i) ≤ ((a.val+1 : ℕ) : ℤ)+k*(n : ℤ)
    omega
  · change ((a.val+1 : ℕ) : ℤ)+k*(n : ℤ) ≤ max (i : ℤ) ((i : ℤ)+d i)
    omega

#print axioms positive_boundary_internal
end LRX.FiniteGaps

import LRX.PacketGapConfinement
import LRX.FiniteWindowRestriction
import LRX.FiniteGapPacketWordBound

/-! The finite filling required by the gap-word theorem is derived from the
absence of packet vertices in the open gap. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem packet_gap_filling {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (W : Window n b) (hoff : W.offset=1) (r : Fin n) (hedge : W.offset+b=r.val)
    (hr : PrunedLift.InCore p d 0 r)
    (hgap : ∀ i, Contains W i → ¬PrunedLift.InCore p d 0 i) :
    ∃ filling : State b, (∀ i, p.symm (embed W i)=embed W (filling i)) ∧
      (∀ i, d (embed W i)=(filling i : ℤ)-(i : ℤ)) := by
  have hncore : ∀ i : Fin n, 0 < i.val → i.val < r.val → ¬PrunedLift.InCore p d 0 i := by
    intro i hi hi'
    apply hgap i
    simp only [Contains]
    omega
  have hbounds (i : Fin n) (hi : Contains W i) :=
    PrunedLift.gap_canonical_displacement hd hcover hroot r hr hncore i
      (by unfold Contains at hi; omega) (by unfold Contains at hi; omega)
  obtain ⟨filling,hmatch⟩ := exists_restriction_of_inverse_closed W p (fun i hi => by
    obtain ⟨_,hlo,hhi⟩ := hbounds i hi
    unfold Contains
    omega)
  refine ⟨filling,hmatch,?_⟩
  intro i
  have h := (hbounds (embed W i) (contains_embed W i)).1
  rw [hmatch] at h
  simpa [embed] using h

#print axioms packet_gap_filling
end LRX.FiniteWindow

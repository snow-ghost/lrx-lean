import LRX.PacketExteriorBudget
import LRX.ExteriorCursorWord

namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem first_exterior_gap_word (hn : 7 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (hload : portLoad d 0=0)
    (hfixed : ∀ i ∈ positions (PrunedLift.core p d 0) 0, d i=0)
    (start finish : Fin n) (hx : start.val ≤ size (PrunedLift.core p d 0) 0)
    (hy : finish.val ≤ size (PrunedLift.core p d 0) 0) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  classical
  let S := PrunedLift.core p d 0
  let W := window S 0
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  have hmov : p⁻¹ 0 ≠ 0 := fun h => hroot (BufferProgram.fixed_short_displacement hd 0 (hshort 0) h)
  have hpartner : p.symm 0 ∈ S := (PrunedLift.mem_core p d 0 _).mpr
    (PrunedLift.in_core_same_cycle p d 0 ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩
      (Equiv.Perm.SameCycle.refl _ _).apply_right)
  have hpos : 0 < (p.symm 0).val := by
    have hne : (p.symm 0).val ≠ 0 := fun h => hmov (Fin.ext h)
    omega
  have hnext : next S 0<n := lt_of_le_of_lt (next_le_member S 0 (p.symm 0) hpartner (by simpa using hpos)) (p.symm 0).isLt
  let r : Fin n := ⟨next S 0,hnext⟩
  have hr : PrunedLift.InCore p d 0 r := by
    obtain ⟨i,hi,he⟩ := next_is_member S 0 hnext
    have hir : i=r := Fin.ext he
    exact (PrunedLift.mem_core p d 0 r).mp (hir ▸ hi)
  have hoff : W.offset=1 := by simp [W,window]
  have hedge : W.offset+size S 0=r.val := by
    have h := lt_next S 0
    dsimp [W,window,size,r]
    simp only [Fin.val_zero] at h ⊢
    omega
  have hzW : ∀ i, FiniteWindow.Contains W i → d i=0 := by
    intro i hi
    exact hfixed i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  have hboundary := FiniteWindow.fixed_window_boundary_load hd W hoff r hedge hzW
  have hzright : portLoad d (r-1)=0 := hboundary.symm.trans hload
  obtain ⟨w,he,hlen⟩ := exterior_cursor_word (by omega) hd hshort hroot hcover r hr
    (size S 0) (by omega) hload hzright start finish hx hy
  have hb := fixed_gap_sharp_budget hn hd hm hroot hcover 0 hfixed
  refine ⟨w,he,?_⟩
  have hbound : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := hlen.trans hb
  exact_mod_cast hbound

#print axioms first_exterior_gap_word
end LRX.FiniteGaps

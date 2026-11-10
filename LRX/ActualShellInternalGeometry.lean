import LRX.ActualShellPrice
import LRX.ActualShallowInternalDeficit

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n r : ℕ} [NeZero n]

/-- Conversely, every selected internal window is a consecutive rank gap
of the actual source core, including windows of size zero. -/
theorem positive_source_window_rank_gap (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (emb : Fin (r+1) ↪o Fin n)
    (himage : ∀ i, i ∈ prefixSourceCore p ↔ ∃ j, emb j=i)
    (B : FillingWindow n) (hB : B ∈ positiveSourceFamily p (componentSet p 0).card) :
    ∃ gap : Fin r, B.window.offset=(emb gap.castSucc).val+1 ∧
      B.size=(emb gap.succ).val-(emb gap.castSucc).val-1 := by
  classical
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hB
  have hu := (mem_positive_source_gap_starts p (componentSet p 0).card u.val).mp u.property
  obtain ⟨v,hv,hvval⟩ := FiniteGaps.next_is_member (sourcePackets p) u.val hu.2.1
  have hnext := FiniteGaps.lt_next (sourcePackets p) u.val
  obtain ⟨_,hright,hwidth⟩ := prefix_component_source_ends p hc (component_card_lt_of_multiple_roots p hm 0)
  have hune : u.val ≠ componentRight p 0 := by
    intro he
    have hz := component_right_port_zero p 0
    rw [← he] at hz
    have hh := hu.2.2.2
    omega
  have huval : u.val.val ≠ (componentRight p 0).val := fun h => hune (Fin.ext h)
  have hub : u.val.val < (componentRight p 0).val := by omega
  have hvbound := FiniteGaps.next_le_member (sourcePackets p) u.val (componentRight p 0) hright hub
  have huc : u.val ∈ prefixSourceCore p := Finset.mem_filter.mpr ⟨hu.1,by omega⟩
  have hvc : v ∈ prefixSourceCore p := Finset.mem_filter.mpr ⟨hv,by omega⟩
  obtain ⟨a,ha⟩ := (himage u.val).mp huc
  obtain ⟨b,hb⟩ := (himage v).mp hvc
  have hab : a.val < b.val := by
    have hh : emb a < emb b := by rw [ha,hb]; change u.val.val < v.val; omega
    exact emb.lt_iff_lt.mp hh
  let gap : Fin r := ⟨a.val,by have := b.isLt; omega⟩
  have hga : gap.castSucc=a := Fin.ext rfl
  have hgb : gap.succ=b := by
    apply Fin.ext
    change a.val+1=b.val
    by_contra h
    have hmid : emb gap.succ ∈ sourcePackets p :=
      (Finset.mem_filter.mp ((himage _).mpr ⟨gap.succ,rfl⟩)).1
    have hlo : u.val.val < (emb gap.succ).val := by
      rw [← ha]
      exact emb.strictMono (by change a.val < a.val+1; omega)
    have hhi : (emb gap.succ).val < FiniteGaps.next (sourcePackets p) u.val := by
      rw [← hvval,← hb]
      exact emb.strictMono (by change a.val+1 < b.val; omega)
    exact (FiniteGaps.gap_avoids_marks (sourcePackets p) u.val (emb gap.succ)
      ((FiniteGaps.mem_positions _ _ _).mpr ⟨hlo,hhi⟩)) hmid
  refine ⟨gap,?_,?_⟩
  · change u.val.val+1=(emb gap.castSucc).val+1
    rw [hga,ha]
  · change FiniteGaps.next (sourcePackets p) u.val-u.val.val-1=
      (emb gap.succ).val-(emb gap.castSucc).val-1
    rw [hgb,hga,hb,ha,hvval]

/-- The rank-geometric deficit is now available for any actual member of
positiveSourceFamily, without a supplied rank/index certificate. -/
theorem prefix_zero_defect_window_internal_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (B : FillingWindow n) (hB : B ∈ positiveSourceFamily p (componentSet p 0).card) :
    let R := (prefixSourceCore p).card
    let t : ℤ := max 0 (2*(B.size : ℤ)-((n-R : ℕ) : ℤ)-(R%2 : ℕ))
    t^2-t%2+8*(t/2)*((n-(componentSet p 0).card : ℕ) : ℤ) ≤ 4*shellH p := by
  obtain ⟨r,emb,hcard,himage,hgeom⟩ := prefix_zero_defect_internal_deficit p hmaj hm hlarge hz
  obtain ⟨gap,_,hsize⟩ := positive_source_window_rank_gap p hm
    (by have := NeZero.pos n; omega) emb himage B hB
  have hh := (hgeom gap).2.2
  rw [← hsize] at hh
  exact hh

#print axioms positive_source_window_rank_gap
#print axioms prefix_zero_defect_window_internal_deficit
end LRX.FiniteCuts

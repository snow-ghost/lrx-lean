import LRX.PrefixShallowPhysicalModel

namespace LRX.FiniteCuts
variable {n r : ℕ} [NeZero n]

/-- Consecutive ranks of the real prefix source core are actual positive
source gaps, hence selected in the existing family of invariant fillings. -/
theorem prefix_rank_gap_selected (p : State n) (emb : Fin (r+1) ↪o Fin n)
    (himage : ∀ i, i ∈ prefixSourceCore p ↔ ∃ j, emb j=i) (gap : Fin r) :
    FiniteGaps.next (sourcePackets p) (emb gap.castSucc)=(emb gap.succ).val ∧
      emb gap.castSucc ∈ positiveSourceGapStarts p (componentSet p 0).card := by
  classical
  have hmem (i : Fin (r+1)) : emb i ∈ prefixSourceCore p := (himage _).mpr ⟨i,rfl⟩
  have hu := Finset.mem_filter.mp (hmem gap.castSucc)
  have hv := Finset.mem_filter.mp (hmem gap.succ)
  have huv : (emb gap.castSucc).val < (emb gap.succ).val :=
    emb.strictMono (by change gap.val < gap.val+1; omega)
  have hgap (x : Fin n) (hx0 : (emb gap.castSucc).val < x.val)
      (hx1 : x.val < (emb gap.succ).val) : x ∉ sourcePackets p := by
    intro hxs
    have hxc : x ∈ prefixSourceCore p := Finset.mem_filter.mpr ⟨hxs,by omega⟩
    obtain ⟨j,rfl⟩ := (himage x).mp hxc
    have h0 : gap.castSucc < j := emb.lt_iff_lt.mp hx0
    have h1 : j < gap.succ := emb.lt_iff_lt.mp hx1
    change gap.val < j.val at h0
    change j.val < gap.val+1 at h1
    omega
  have hpu := (CycleFootprint.mem_component _ _ _).mp ((zero_component_prefix p _).mpr hu.2)
  have hpv := (CycleFootprint.mem_component _ _ _).mp ((zero_component_prefix p _).mpr hv.2)
  have hpath := (CycleFootprint.load_path_symm _ hpu).trans hpv
  have hpos := load_path_crossed_port_positive p hpath (emb gap.castSucc) (by omega) huv
  exact consecutive_positive_gap_selected p (componentSet p 0).card _ _ hu.1 hv.1 huv hgap hpos (by omega)

#print axioms prefix_rank_gap_selected
end LRX.FiniteCuts

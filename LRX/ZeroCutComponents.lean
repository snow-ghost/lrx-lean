module

public import LRX.LoadPathRecenter

@[expose] public section

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem zero_cut_multiple_components (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (z : Fin n)
    (hz : portLoad (displacement p.symm) z=0) :
    1 < (componentRoots (localTarget p 0 (z+1))).card := by
  classical
  let r := z+1
  let q := localTarget p 0 r
  let a := componentOrder p hc 0
  let b := componentOrder p hc (Fin.last k)
  have ha := component_order_mem p hc 0
  have hb := component_order_mem p hc (Fin.last k)
  have hab : a.val < b.val := (componentOrder p hc).strictMono (by change 0 < k; exact hk)
  have hnot : ¬CycleFootprint.LoadPath (displacement p.symm) a b := by
    intro hp
    have he := component_roots_unique p ha hb hp
    have hh := congrArg Fin.val he
    omega
  have ham : a-r ∈ q.support := by
    apply (recentered_mem_support p r (a-r)).mpr
    simpa only [sub_add_cancel] using (mem_support_inverse p a).mpr (component_root_moved p a ha)
  have hbm : b-r ∈ q.support := by
    apply (recentered_mem_support p r (b-r)).mpr
    simpa only [sub_add_cancel] using (mem_support_inverse p b).mpr (component_root_moved p b hb)
  obtain ⟨u,hu,hua⟩ := component_roots_cover q (a-r) ((mem_support_inverse q _).mp ham)
  obtain ⟨v,hv,hvb⟩ := component_roots_cover q (b-r) ((mem_support_inverse q _).mp hbm)
  have huv : u ≠ v := by
    intro he
    have hp := (CycleFootprint.load_path_symm _ hua).trans (he ▸ hvb)
    have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
      simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
    have hcan := phase_zero_cut_canonical 0 z hd hz
    change localDisplacement (displacement p.symm) r=displacement q.symm at hcan
    rw [← hcan] at hp
    have hh := (load_path_recenter (displacement p.symm) r (a-r) (b-r)).mp hp
    exact hnot (by simpa only [sub_add_cancel] using hh)
  exact Finset.one_lt_card.mpr ⟨u,hu,v,hv,huv⟩

#print axioms zero_cut_multiple_components
end LRX.FiniteCuts

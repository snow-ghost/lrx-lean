import LRX.AreaWindowSizeBounds

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- C5's size restrictions with every core, interval and count extracted from
an original selected large proper component. -/
theorem component_area_size_bounds (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (hproper : (componentSet p root).card < n) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let As := areaWindowFamily q L
    let V := (As.map (fun A => A.size)).sum
    let t := (nontrivialSuffixComponents q L).card
    4 ≤ (prefixSourceCore q).card ∧
      (∀ A ∈ As, A.size ≤ n/2-1) ∧
      V ≤ 2*(n/2-1) ∧ 2*t ≤ V ∧
      t ≤ (As.filter (fun A => decide (2 ≤ A.size))).length ∧
      (As.map (fun A => (A.size : ℤ)^2)).sum ≤ ((n/2-1 : ℕ) : ℤ)*(V : ℤ) := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hzero : (componentSet q 0).card = (componentSet p root).card := by
    have h := (component_recenter_cut p root).2 0
    simp only [zero_add] at h
    have he : componentSet p root = componentSet p r :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card = (componentSet p r).card at h
    rwa [← he] at h
  have hz := component_left_port_zero p root
  have hr : componentLeft p root-1+1 = r := by dsimp [r]; ring
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hqm := phase_zero_cut_majorized 0 (componentLeft p root-1) hd hmaj hz
  rw [hr] at hqm
  have hlarge' : (n+1)/2 < (componentSet q 0).card := by omega
  have hproper' : (componentSet q 0).card < n := by omega
  have hcore := large_prefix_source_core_card q hqm hlarge' hproper'
  have hsize := area_window_size_cap q hqm hlarge' hproper'
  have htotal := area_window_total_size_cap q hqm hlarge' hproper'
  have hlower := area_window_total_size_lower q (componentSet q 0).card
  have hcount := area_family_nontrivial_count q (componentSet q 0).card
  have hsquare := area_window_square_sum_cap q hqm hlarge' hproper'
  dsimp only at hsquare ⊢
  rw [hzero] at hsize htotal hlower hcount hsquare
  refine ⟨hcore,hsize,htotal,hlower,hcount,?_⟩
  simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hsquare

#print axioms component_area_size_bounds
end LRX.FiniteCuts

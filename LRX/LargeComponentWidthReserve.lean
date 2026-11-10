import LRX.LargeComponentBridgeReserve

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

theorem cross_minimum_pays_gap_width (t v a pairs M : ℤ)
    (ht : 2 ≤ t) (hv : 2*t ≤ v) (ha : 0 ≤ a) (hpairs : 0 ≤ pairs)
    (hM : 2*(t-1)*(v-t)+a*v+pairs ≤ M) : 3*a+2*t ≤ M := by
  have h1 := mul_nonneg (show 0 ≤ t-1 by omega) (show 0 ≤ v-2*t by omega)
  have h2 := mul_nonneg (show 0 ≤ t by omega) (show 0 ≤ t-2 by omega)
  have h3 := mul_nonneg ha (show 0 ≤ v-3 by omega)
  nlinarith

theorem component_cut_isolated_count (p : State n) (root : Fin n)
    (hsize : 2 ≤ (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    (isolatedVertices q).card = (singletonSuffixComponents q (componentSet p root).card).card := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  let L := (componentSet p root).card
  have he : componentSet p root = componentSet p r :=
    CycleFootprint.component_eq_of_path _ (component_left_path p root)
  have hzero : (componentSet q 0).card = L := by
    have h := (component_recenter_cut p root).2 0
    simp only [zero_add] at h
    change (componentSet q 0).card = (componentSet p r).card at h
    rw [← he] at h
    exact h
  have hc : 2 ≤ (componentSet q 0).card := by rw [hzero]; exact hsize
  have hpref (i : Fin n) : i ∈ componentSet q 0 ↔ i.val < L := by rw [zero_component_prefix,hzero]
  have hs := prefix_singleton_components q L hc hpref
  change (isolatedVertices q).card = (singletonSuffixComponents q L).card
  rw [isolated_vertices_card,hs]

end LRX.FiniteCuts

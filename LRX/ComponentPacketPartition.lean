module

public import LRX.CanonicalPacketPeakService
public import LRX.SourcePacketEventCover
public import LRX.FiniteGlobalPeak

@[expose] public section

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The actual packet support records both original movement and core membership. -/
theorem mem_canonical_packet_support (p : State n) (r i : Fin n) :
    i ∈ (canonicalRootPacket p r).support ↔
      i ∈ p.support ∧ PrunedLift.InCore p (displacement p.symm) r i := by
  classical
  simp only [canonicalRootPacket,Equiv.Perm.mem_support,PrunedLift.permutation_apply]
  by_cases hi : i ∈ PrunedLift.core p (displacement p.symm) r
  · simp [hi,(PrunedLift.mem_core p (displacement p.symm) r i).mp hi]
  · have hh := mt (PrunedLift.mem_core p (displacement p.symm) r i).mpr hi
    simp [hi,hh]

theorem distinct_component_packets_disjoint (p : State n) (a b : Fin n)
    (ha : a ∈ componentRoots p) (hb : b ∈ componentRoots p) (hne : a ≠ b) :
    (canonicalRootPacket p a).Disjoint (canonicalRootPacket p b) := by
  classical
  rw [Equiv.Perm.disjoint_iff_disjoint_support]
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := (mem_canonical_packet_support p a i).mp hi
  have hj' := (mem_canonical_packet_support p b i).mp hj
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hai := CycleFootprint.service_path_load_path hd hi'.2.1
  have hib := CycleFootprint.service_path_load_path hd hj'.2.2
  exact hne (component_roots_unique p ha hb (hai.trans hib))

/-- Distinct real component roots give pairwise disjoint packet targets. -/
theorem component_packet_list_disjoint (p : State n) (roots : List (Fin n))
    (hnd : roots.Nodup) (hr : ∀ r ∈ roots, r ∈ componentRoots p) :
    (roots.map (canonicalRootPacket p)).Pairwise Equiv.Perm.Disjoint := by
  apply List.pairwise_map.mpr
  exact hnd.imp_of_mem (fun {a b} ha hb hne =>
    distinct_component_packets_disjoint p a b (hr a ha) (hr b hb) hne)

/-- If every moving vertex is a source vertex, the real component packets
exhaust the original permutation. No product factorization is supplied. -/
theorem component_packet_list_product (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (roots : List (Fin n))
    (hnd : roots.Nodup) (hr : ∀ r, r ∈ roots ↔ r ∈ componentRoots p)
    (hsource : ∀ i ∈ p.support, i ∈ sourcePackets p) :
    (roots.map (canonicalRootPacket p)).prod=p := by
  classical
  have hdis := component_packet_list_disjoint p roots hnd (fun r h => (hr r).mp h)
  apply Equiv.ext
  intro i
  by_cases hi : i ∈ p.support
  · have hmove := (mem_support_inverse p i).mp hi
    obtain ⟨r,hrr,hpath⟩ := component_roots_cover p i hmove
    have hri := component_root_reaches hn p hm r hrr i hmove hpath
    have his := (mem_source_packets p i).mp (hsource i hi)
    have hc : PrunedLift.InCore p (displacement p.symm) r i := ⟨hri,his.2 r hri⟩
    have hip := (mem_canonical_packet_support p r i).mpr ⟨hi,hc⟩
    have he := Equiv.Perm.eq_on_support_mem_disjoint
      (List.mem_map.mpr ⟨r,(hr r).mpr hrr,rfl⟩) hdis i hip
    rw [← he]
    simp only [canonicalRootPacket,PrunedLift.permutation_apply,
      (PrunedLift.mem_core p (displacement p.symm) r i).mpr hc,ite_eq_left]
  · have hfix : p i=i := Equiv.Perm.notMem_support.mp hi
    have hall : ∀ q ∈ roots.map (canonicalRootPacket p), q i=i := by
      intro q hq
      obtain ⟨r,_,rfl⟩ := List.mem_map.mp hq
      simp [canonicalRootPacket,PrunedLift.permutation_apply,hfix]
    have aux (qs : List (State n)) (hh : ∀ q ∈ qs, q i=i) : qs.prod i=i := by
      induction qs with
      | nil => rfl
      | cons q qs ih =>
        simp only [List.prod_cons,Equiv.Perm.mul_apply]
        rw [ih (fun z hz => hh z (List.mem_cons_of_mem _ hz))]
        exact hh q (by simp)
    exact (aux _ hall).trans hfix.symm

/-- Absence of actual filling cycles forces every moving vertex into a source packet. -/
theorem source_covers_of_no_fillings (p : State n) (hf : fillingCycles p=∅)
    (i : Fin n) (hi : i ∈ p.support) : i ∈ sourcePackets p := by
  classical
  by_contra hs
  have hinv : i ∈ (p⁻¹).support := by simpa only [Equiv.Perm.support_inv] using hi
  obtain ⟨q,hq,hiq⟩ := (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).mp hinv
  have hqfill : q ∈ fillingCycles p := by
    apply Finset.mem_filter.mpr
    refine ⟨hq,Finset.disjoint_left.mpr ?_⟩
    intro j hj hjs
    have hc := (ZeroGap.cycle_root_same_cycle hq hiq).symm.trans
      (ZeroGap.cycle_root_same_cycle hq hj)
    exact hs (source_packets_predecessor_closed p i j (Or.inl hc) hjs)
  rw [hf] at hqfill
  exact Finset.notMem_empty q hqfill

theorem component_packet_peak_positive (p : State n) (r : Fin n)
    (hr : r ∈ componentRoots p) : 0 < leftPeak (canonicalRootPacket p r).symm n := by
  have hm := component_root_moved p r hr
  apply moved_global_peak_positive _ r
  simpa only [canonicalRootPacket,PrunedLift.permutation_symm_apply,
    PrunedLift.mem_core,PrunedLift.InCore,Relation.ReflTransGen.refl,
    and_self,ite_true] using hm

#print axioms component_packet_list_disjoint
#print axioms component_packet_list_product
end LRX.FiniteCuts

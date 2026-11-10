import LRX.ShallowShellWindowFamily

/-! M4: the scalar internal-hole size x is exactly the sum of the actual
positive prefix window widths, not the size of the larger C9 family. -/
namespace LRX.FiniteCuts
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

theorem prefix_internal_size_partition (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    ((positiveSourceFamily p (componentSet p 0).card).map (fun A => A.size)).sum+
      (prefixSourceCore p).card=(componentSet p 0).card := by
  classical
  let As := positiveSourceFamily p (componentSet p 0).card
  have hspec := positive_source_family_spec p (componentSet p 0).card
  have hcover : familyPositions As ∪ prefixSourceCore p=componentSet p 0 := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨A,hA,hiA⟩ := (mem_family_positions As i).mp hi
        have he := hspec.2.2.1 A hA
        apply (zero_component_prefix p i).mpr
        unfold Contains at hiA
        omega
      · exact (zero_component_prefix p i).mpr (Finset.mem_filter.mp hi).2
    · intro hi
      have hiL := (zero_component_prefix p i).mp hi
      by_cases hs : i ∈ sourcePackets p
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hs,hiL⟩))
      · exact Finset.mem_union.mpr (Or.inl (prefix_non_source_in_positive_family p hc hproper i hiL hs))
  have hdis : Disjoint (familyPositions As) (prefixSourceCore p) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨A,hA,hiA⟩ := (mem_family_positions As i).mp hi
    exact positive_family_avoids_source p _ A hA i (Finset.mem_filter.mp hj).1 hiA
  have hcard := congrArg Finset.card hcover
  rw [Finset.card_union_of_disjoint hdis] at hcard
  have he := (window_family_selected_energy As p.symm hspec.1 hspec.2.1).1
  rw [he] at hcard
  exact hcard

theorem component_cut_internal_size_partition (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hsize : 2 ≤ (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    ((positiveSourceFamily q (componentSet p root).card).map (fun A => A.size)).sum+
      (prefixSourceCore q).card=(componentSet p root).card := by
  let q := localTarget p 0 (componentLeft p root)
  have hzero : (componentSet q 0).card=(componentSet p root).card := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have he : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← he] at hh
  have hproper := component_card_lt_of_multiple_roots p hm root
  have hh := prefix_internal_size_partition q (by omega) (by omega)
  rw [hzero] at hh
  exact hh

#print axioms prefix_internal_size_partition
#print axioms component_cut_internal_size_partition
end LRX.FiniteCuts

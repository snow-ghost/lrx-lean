import LRX.TwoVertexSourceCover

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_peak_four_no_fillings (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : sourceHalfPeak p=4)
 : fillingCycles p=∅ := by
  classical
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hzero : (componentSet q 0).card=L := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have hh' : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← hh'] at hh
  have hsize : 2 ≤ L := by dsimp only [L]; omega
  have hproper : L<n := component_card_lt_of_multiple_roots p (by omega) root
  have hroots : (componentRoots q).card=(componentRoots p).card := by
    rw [component_roots_card_eq_blocks,component_roots_card_eq_blocks]
    exact component_cut_nontrivial_count p root
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hqe : canonicalEnergyDeficit q=0 := by
    unfold canonicalEnergyDeficit
    dsimp only [q]
    rw [component_cut_displacement_mass]
    exact he
  have hf := zero_energy_even_full_support q hqm hqe hp
  have hfull : q.support=Finset.univ :=
    Finset.eq_univ_of_card q.support (by simpa only [Fintype.card_fin] using hf)
  have hrig := peak_four_source_rigidity hn p hmaj hmax hc hk root hlarge ht hpos he hp hv hU
  have hcount := component_cut_external_count p root hsize
  have ht2 : (nontrivialSuffixComponents q L).card=2 := by
    change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
    have hh := hrig.1
    omega
  change (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ)=4 at hv
  have hsource (i : Fin n) : i ∈ sourcePackets q := by
    by_cases hi : i.val<L
    · by_contra hout
      have hmem := prefix_non_source_in_positive_family q (by omega) (by omega) i (by omega) hout
      rw [hzero] at hmem
      obtain ⟨A,hA,hiA⟩ := (mem_family_positions _ _).mp hmem
      have hz := actual_peak_four_filling_size_zero hn p hmaj hmax hc hk root hlarge ht hpos he hp hv hU A hA
      have hb := hiA.1
      have he' := hiA.2
      omega
    · have hmove : q.symm i ≠ i := (mem_support_inverse q i).mp (by rw [hfull]; exact Finset.mem_univ _)
      have hd : AffineLift.IsLift q 0 (displacement q.symm) := by
        simpa only [Equiv.symm_symm] using canonical_lift q.symm
      have hii : i ∈ componentSet q i := (CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl
      have hip : q.symm i ∈ componentSet q i := by
        have hh := CycleFootprint.component_invariant hd i (q.symm i)
        rw [Equiv.apply_symm_apply] at hh
        exact hh.mp hii
      have hcard : 2 ≤ (componentSet q i).card :=
        Finset.one_lt_card.mpr ⟨i,hii,q.symm i,hip,Ne.symm hmove⟩
      have hmem : componentSet q i ∈ nontrivialSuffixComponents q L := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_image.mpr ⟨i,(mem_suffix_vertices L i).mpr (by omega),rfl⟩,hcard⟩
      have hrest := Finset.sum_le_sum (s := (nontrivialSuffixComponents q L).erase (componentSet q i))
        (f := fun _ => (2 : ℕ)) (g := fun C => C.card)
        (fun C hC => (Finset.mem_filter.mp (Finset.mem_of_mem_erase hC)).2)
      simp only [Finset.sum_const,Finset.card_erase_of_mem hmem,ht2] at hrest
      norm_num only [Nat.reduceSub,one_nsmul] at hrest
      have hsum := Finset.sum_erase_add (nontrivialSuffixComponents q L) (fun C => C.card) hmem
      rw [hv] at hsum
      apply two_vertex_component_source hn q (by omega) i hmove
      omega
  have hfillq : fillingCycles q=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hcf
    obtain ⟨hcycle,hdis⟩ := Finset.mem_filter.mp hcf
    obtain ⟨i,hi⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1.nonempty_support
    exact Finset.disjoint_left.mp hdis hi (hsource i)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hcf
  have hcq := (filling_cycle_recenter_iff p c (componentLeft p root)
    (component_cut_canonical_displacement p root)).mpr hcf
  change localTarget c 0 (componentLeft p root) ∈ fillingCycles q at hcq
  rw [hfillq] at hcq
  exact Finset.notMem_empty _ hcq

#print axioms actual_peak_four_no_fillings
end LRX.FiniteCuts

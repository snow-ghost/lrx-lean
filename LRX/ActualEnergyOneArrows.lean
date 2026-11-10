import LRX.EnergyOneArrowCertificate
import LRX.ExternalFixedPositionsExhaust

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_energy_one_nonempty_shape (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=1) (hp : n%2=0)
    (f : ℕ) (hf : f ≤ 2) (hfix : n-p.support.card=f)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=(if f=0 then 4 else 6)) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    (singletonSuffixComponents q L).card=0 ∧
      ∀ i : Fin n, i.val < L → (if f=2 then 3 else 2) ≤ |displacement q.symm i| := by
  classical
  obtain ⟨A,B,hlist,hma,hmb,hab,hmem⟩ :=
    actual_unpaid_filtered_exterior_pair hn p hmaj hmax hc hk root hlarge ht hpos
  rw [hp,he,hfix,hv] at hmem
  norm_num only [Nat.cast_zero] at hmem
  have hmem' := filtered_catalogue_drop_isolated _ _ _ _ _ _ _ hmem
  have hlocalFixed := energy_one_pair_fixed_count _ _ f hf hmem'
  have hbudget := ((filtered_catalogue_mem_iff _ _ _ _ _ _ _).mp hmem).2.2.1.2
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have ha0 : (singletonSuffixComponents q L).card=0 := by
    change (A.size-A.filling.support.card)+(B.size-B.filling.support.card)+
      (singletonSuffixComponents q L).card ≤ f at hbudget
    change (A.size-A.filling.support.card)+(B.size-B.filling.support.card)=f at hlocalFixed
    omega
  change suffixComponentFamily q L=[A,B] at hlist
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hqe : canonicalEnergyDeficit q=1 := by
    unfold canonicalEnergyDeficit
    dsimp only [q]
    rw [component_cut_displacement_mass]
    exact he
  have hqs : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have hsum : positiveSignOffset q+negativeSignOffset q=(f : ℤ) := by
    have hh := signed_offsets_sum q
    rw [hqs,hfix,hp] at hh
    simpa only [Nat.cast_zero,sub_zero] using hh
  have hbounds := (actual_sign_offset_bounds q hqm).1
  rw [hqe] at hbounds
  norm_num only at hbounds
  have hpair : LocalPairSignConstraints A.filling B.filling 0 1
      (positiveSignOffset q) (negativeSignOffset q) := by
    constructor
    · intro S T hS hT
      have hh := two_window_positive_selection A B q hqm hma hmb hab S T hS hT
      simpa only [hp,hqe,Nat.cast_zero] using hh
    · intro S T hS hT
      have hh := two_window_negative_selection A B q hqm hma hmb hab S T hS hT
      simpa only [hp,hqe,Nat.cast_zero] using hh
  have hfamilyMatch : ∀ C ∈ ([A,B] : List (FillingWindow n)), C.Matches q.symm := by
    intro C hC
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hC
    rcases hC with rfl | rfl
    · exact hma
    · exact hmb
  have hfamilyApart : ([A,B] : List (FillingWindow n)).Pairwise FillingWindow.Apart := by
    simpa [List.pairwise_cons] using hab
  have hfamilyFixed : (([A,B] : List (FillingWindow n)).map
      (fun C => C.size-C.filling.support.card)).sum=n-(Equiv.Perm.support q.symm).card := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change (A.size-A.filling.support.card)+(B.size-B.filling.support.card)=n-(q⁻¹).support.card
    rw [Equiv.Perm.support_inv,hqs,hfix]
    exact hlocalFixed
  have hLn : L ≤ n := by
    simpa only [L,Fintype.card_fin] using Finset.card_le_univ (componentSet p root)
  have hboundary := (suffix_component_family_spec q L hLn (component_recenter_cut p root).1).2.2
  have hAb : L ≤ A.window.offset := hboundary A (by rw [hlist]; simp)
  have hBb : L ≤ B.window.offset := hboundary B (by rw [hlist]; simp)
  change (singletonSuffixComponents q L).card=0 ∧
    ∀ i : Fin n, i.val < L → (if f=2 then 3 else 2) ≤ |displacement q.symm i|
  refine ⟨ha0,?_⟩
  intro i hi
  have hia : ¬Contains A.window i := by intro h; have hh := h.1; omega
  have hib : ¬Contains B.window i := by intro h; have hh := h.1; omega
  have hout : i ∉ familyPositions ([A,B] : List (FillingWindow n)) := by
    intro hh
    obtain ⟨C,hC,hCi⟩ := (mem_family_positions _ i).mp hh
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hC
    rcases hC with rfl | rfl
    · exact hia hCi
    · exact hib hCi
  have hmove := full_fixed_count_family_moves_outside [A,B] q.symm hfamilyMatch hfamilyApart hfamilyFixed i hout
  have hzero : displacement q.symm i ≠ 0 := by
    intro hz
    apply hmove
    apply Fin.ext
    unfold displacement at hz
    omega
  have hlen : 0 < |displacement q.symm i| := abs_pos.mpr hzero
  by_contra hh
  have hsmall : |displacement q.symm i|=1 ∨ (f=2 ∧ |displacement q.symm i|=2) := by
    by_cases hf2 : f=2
    · rw [if_pos hf2] at hh
      omega
    · rw [if_neg hf2] at hh
      omega
  have hforbid := energy_one_pair_forbids_extra _ _ f hf hmem' _ _ hsum hbounds.1 hbounds.2 hpair
  by_cases hs : 0 < displacement q.symm i
  · have hcst := actual_offset_extra_arrow_constraint A B q hqm hma hmb hab i hia hib
      1 (Or.inl rfl) (by simpa using hs)
    rw [hp,hqe] at hcst
    exact hforbid 1 _ (Or.inl rfl) hsmall hcst
  · have hcst := actual_offset_extra_arrow_constraint A B q hqm hma hmb hab i hia hib
      (-1) (Or.inr rfl) (by simp only [neg_one_mul]; omega)
    rw [hp,hqe] at hcst
    exact hforbid (-1) _ (Or.inr rfl) hsmall hcst

#print axioms actual_energy_one_nonempty_shape
end LRX.FiniteCuts

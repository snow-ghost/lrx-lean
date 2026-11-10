import LRX.ExtraArrowSignConstraint
import LRX.ZeroEnergyEmptyCatalogues

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem even_width_six_extra_arrow_check :
    (filteredExteriorCatalogue 0 0 0 0 6).all (fun z => decide
      (∀ s : Fin 2, ∀ l : Fin 2, ¬ExtraArrowSignConstraint z.1.2 z.2.2
        (if s.val=0 then 1 else -1) ((l.val : ℤ)+1)))=true := by
  decide +kernel

theorem even_width_six_forbids_extra (A B : SmallExteriorMap)
    (hm : (A,B) ∈ filteredExteriorCatalogue 0 0 0 0 6)
    (sign len : ℤ) (hs : sign=1 ∨ sign= -1) (hl : len=1 ∨ len=2) :
    ¬ExtraArrowSignConstraint A.2 B.2 sign len := by
  have hh := of_decide_eq_true (List.all_eq_true.mp even_width_six_extra_arrow_check (A,B) hm)
  rcases hs with rfl | rfl <;> rcases hl with rfl | rfl
  · simpa using hh 0 0
  · simpa using hh 0 1
  · simpa using hh 1 0
  · simpa using hh 1 1

variable {n k : ℕ} [NeZero n]

theorem actual_even_zero_width_six_large_min_arrow (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=6) :
    let q := localTarget p 0 (componentLeft p root)
    ∀ i : Fin n, i.val < (componentSet p root).card → 3 ≤ |displacement q.symm i| := by
  obtain ⟨A,B,hlist,hma,hmb,hab,hmem⟩ :=
    actual_unpaid_filtered_exterior_pair hn p hmaj hmax hc hk root hlarge ht hpos
  have hf : n-p.support.card=0 := by
    have hh := zero_energy_even_full_support p hmaj he hp
    omega
  have hmem' := filtered_catalogue_drop_isolated _ _ _ _ _ _ _ hmem
  rw [hp,he,hf,hv] at hmem'
  norm_num only [Nat.cast_zero] at hmem'
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  change suffixComponentFamily q L=[A,B] at hlist
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hqe : canonicalEnergyDeficit q=0 := by
    unfold canonicalEnergyDeficit
    dsimp only [q]
    rw [component_cut_displacement_mass]
    exact he
  have hfull : q.support=Finset.univ := Finset.eq_univ_of_card q.support
    (by simpa only [Fintype.card_fin] using zero_energy_even_full_support q hqm hqe hp)
  have hLn : L ≤ n := by
    simpa only [L,Fintype.card_fin] using Finset.card_le_univ (componentSet p root)
  have hboundary := (suffix_component_family_spec q L hLn (component_recenter_cut p root).1).2.2
  have hAb : L ≤ A.window.offset := hboundary A (by rw [hlist]; simp)
  have hBb : L ≤ B.window.offset := hboundary B (by rw [hlist]; simp)
  change ∀ i : Fin n, i.val < L → 3 ≤ |displacement q.symm i|
  intro i hi
  have hia : ¬Contains A.window i := by intro h; have hh := h.1; omega
  have hib : ¬Contains B.window i := by intro h; have hh := h.1; omega
  have hmove : q.symm i ≠ i := (mem_support_inverse q i).mp (by rw [hfull]; exact Finset.mem_univ _)
  have hzero : displacement q.symm i ≠ 0 := by
    intro hz
    apply hmove
    apply Fin.ext
    unfold displacement at hz
    omega
  have hlen : 0 < |displacement q.symm i| := abs_pos.mpr hzero
  by_contra hh
  have hsmall : |displacement q.symm i|=1 ∨ |displacement q.symm i|=2 := by omega
  by_cases hs : 0 < displacement q.symm i
  · have hcst := actual_extra_arrow_sign_constraint A B q hqm hqe hp hma hmb hab i hia hib
      1 (Or.inl rfl) (by simpa using hs)
    exact even_width_six_forbids_extra _ _ hmem' 1 _ (Or.inl rfl) hsmall hcst
  · have hcst := actual_extra_arrow_sign_constraint A B q hqm hqe hp hma hmb hab i hia hib
      (-1) (Or.inr rfl) (by simp only [neg_one_mul]; omega)
    exact even_width_six_forbids_extra _ _ hmem' (-1) _ (Or.inr rfl) hsmall hcst

#print axioms even_width_six_extra_arrow_check
#print axioms even_width_six_forbids_extra
#print axioms actual_even_zero_width_six_large_min_arrow
end LRX.FiniteCuts

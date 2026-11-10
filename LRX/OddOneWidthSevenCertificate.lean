import LRX.WidthSevenChecks.Case25
import LRX.WidthSevenChecks.Case34
import LRX.WidthSevenChecks.Case43
import LRX.WidthSevenChecks.Case52
import LRX.OffsetExtraArrowSignConstraint
import LRX.OddWidthFiveWindowArrows
import LRX.ZeroEnergyEmptyCatalogues

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem odd_one_seven_arrow_check :
    (filteredExteriorCatalogue 1 0 1 0 7).all (fun z => decide
      (((∃ i, z.1.2 i=i) ∨ (∃ i, z.2.2 i=i)) ∧
       (∀ s : Fin 2, ∀ l : Fin 2, ¬OffsetExtraArrowSignConstraint z.1.2 z.2.2 1 0 0
          (if s.val=0 then 1 else -1) ((l.val : ℤ)+1))))=true := by
  apply List.all_eq_true.mpr
  rintro ⟨A,B⟩ hm
  apply decide_eq_true
  change SevenArrowConclusion A B
  obtain ⟨ha,hb,⟨hw,hf⟩,hc⟩ := (filtered_catalogue_mem_iff A B 1 0 1 0 7).mp hm
  exact (width_seven_cases A B ha hb hw SevenArrowGuard
    seven_arrow_25 seven_arrow_34 seven_arrow_43 seven_arrow_52) hf hc

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem odd_one_seven_isolated_empty : filteredExteriorCatalogue 1 0 1 1 7=[] := by
  decide +kernel

theorem odd_one_seven_forbids_extra (A B : SmallExteriorMap)
    (hm : (A,B) ∈ filteredExteriorCatalogue 1 0 1 0 7)
    (sign len : ℤ) (hs : sign=1 ∨ sign= -1) (hl : len=1 ∨ len=2) :
    ¬OffsetExtraArrowSignConstraint A.2 B.2 1 0 0 sign len := by
  have hh := (of_decide_eq_true (List.all_eq_true.mp odd_one_seven_arrow_check (A,B) hm)).2
  rcases hs with rfl | rfl <;> rcases hl with rfl | rfl
  · simpa using hh 0 0
  · simpa using hh 0 1
  · simpa using hh 1 0
  · simpa using hh 1 1

variable {n k : ℕ} [NeZero n]
theorem actual_odd_one_width_seven_large_min_arrow (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=7) :
    let q := localTarget p 0 (componentLeft p root)
    ∀ i : Fin n, i.val < (componentSet p root).card → 3 ≤ |displacement q.symm i| := by
  obtain ⟨A,B,hlist,hma,hmb,hab,hmem⟩ :=
    actual_unpaid_filtered_exterior_pair hn p hmaj hmax hc hk root hlarge ht hpos
  have hmem' := filtered_catalogue_drop_isolated _ _ _ _ _ _ _ hmem
  rw [hp,he,hf,hv] at hmem'
  norm_num only [Nat.cast_one] at hmem'
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
  have hqs : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have hqf : n-q.support.card=1 := by rwa [hqs]
  obtain ⟨hP,hN⟩ := zero_energy_odd_one_fixed_sign_offsets q hqm hqe hp hqf
  have hfixed := (of_decide_eq_true (List.all_eq_true.mp odd_one_seven_arrow_check
    (⟨A.size,A.filling⟩,⟨B.size,B.filling⟩) hmem')).1
  have hLn : L ≤ n := by
    simpa only [L,Fintype.card_fin] using Finset.card_le_univ (componentSet p root)
  have hboundary := (suffix_component_family_spec q L hLn (component_recenter_cut p root).1).2.2
  have hAb : L ≤ A.window.offset := hboundary A (by rw [hlist]; simp)
  have hBb : L ≤ B.window.offset := hboundary B (by rw [hlist]; simp)
  change ∀ i : Fin n, i.val < L → 3 ≤ |displacement q.symm i|
  intro i hi
  have hia : ¬Contains A.window i := by intro h; have hh := h.1; omega
  have hib : ¬Contains B.window i := by intro h; have hh := h.1; omega
  have hzero : displacement q.symm i ≠ 0 := by
    intro hz
    have hiFix : q.symm i=i := by apply Fin.ext; unfold displacement at hz; omega
    rcases hfixed with ⟨c,hcFix⟩ | ⟨c,hcFix⟩
    · have hcq : q.symm (embed A.window c)=embed A.window c := by rw [hma c,hcFix]
      have hh := one_fixed_position_unique q hqf _ i hcq hiFix
      exact hia (hh ▸ contains_embed A.window c)
    · have hcq : q.symm (embed B.window c)=embed B.window c := by rw [hmb c,hcFix]
      have hh := one_fixed_position_unique q hqf _ i hcq hiFix
      exact hib (hh ▸ contains_embed B.window c)
  have hlen : 0 < |displacement q.symm i| := abs_pos.mpr hzero
  by_contra hh
  have hsmall : |displacement q.symm i|=1 ∨ |displacement q.symm i|=2 := by omega
  by_cases hs : 0 < displacement q.symm i
  · have hcst := actual_offset_extra_arrow_constraint A B q hqm hma hmb hab i hia hib
      1 (Or.inl rfl) (by simpa using hs)
    simp only [hp,hqe,Nat.cast_one,hP,hN,ite_self] at hcst
    exact odd_one_seven_forbids_extra _ _ hmem' 1 _ (Or.inl rfl) hsmall hcst
  · have hcst := actual_offset_extra_arrow_constraint A B q hqm hma hmb hab i hia hib
      (-1) (Or.inr rfl) (by simp only [neg_one_mul]; omega)
    simp only [hp,hqe,Nat.cast_one,hP,hN,ite_self] at hcst
    exact odd_one_seven_forbids_extra _ _ hmem' (-1) _ (Or.inr rfl) hsmall hcst


#print axioms odd_one_seven_arrow_check
#print axioms odd_one_seven_isolated_empty
#print axioms odd_one_seven_forbids_extra
#print axioms actual_odd_one_width_seven_large_min_arrow
end LRX.FiniteCuts

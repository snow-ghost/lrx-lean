module

public import LRX.OffsetExtraArrowSignConstraint
public import LRX.ZeroEnergyEmptyCatalogues

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem odd_full_five_extra_arrow_check :
    (filteredExteriorCatalogue 1 0 0 0 5).all (fun z => decide
      (∀ j : Fin 5, let xp := (j.val : ℤ)-2; let xm := -1-xp
        LocalPairSignConstraints z.1.2 z.2.2 1 0 xp xm →
        ∀ s : Fin 2, ∀ l : Fin 2, ¬OffsetExtraArrowSignConstraint z.1.2 z.2.2 1 0
          (if s.val=0 then xp else xm) (if s.val=0 then 1 else -1) ((l.val : ℤ)+1)))=true := by
  decide +kernel

theorem odd_full_five_forbids_extra (A B : SmallExteriorMap)
    (hm : (A,B) ∈ filteredExteriorCatalogue 1 0 0 0 5)
    (xp xm : ℤ) (hsum : xp+xm= -1) (hlo : -2 ≤ xp) (hhi : xp ≤ 2)
    (hc : LocalPairSignConstraints A.2 B.2 1 0 xp xm)
    (sign len : ℤ) (hs : sign=1 ∨ sign= -1) (hl : len=1 ∨ len=2) :
    ¬OffsetExtraArrowSignConstraint A.2 B.2 1 0
      (if sign=1 then xp else xm) sign len := by
  have hh := of_decide_eq_true (List.all_eq_true.mp odd_full_five_extra_arrow_check (A,B) hm)
  let j : Fin 5 := ⟨(xp+2).toNat,by omega⟩
  have hj : (j.val : ℤ)-2=xp := by dsimp only [j]; omega
  have hm' : -1-xp=xm := by omega
  have h := hh j
  dsimp only at h
  rw [hj,hm'] at h
  have h' := h hc
  rcases hs with rfl | rfl <;> rcases hl with rfl | rfl
  · simpa using h' 0 0
  · simpa using h' 0 1
  · simpa using h' 1 0
  · simpa using h' 1 1

variable {n k : ℕ} [NeZero n]

theorem actual_odd_full_width_five_large_min_arrow (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=5) :
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
  have hqfull : q.support.card=n := by
    have hh : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
    omega
  have hfull : q.support=Finset.univ := Finset.eq_univ_of_card q.support
    (by simpa only [Fintype.card_fin] using hqfull)
  have hsum : positiveSignOffset q+negativeSignOffset q= -1 := by
    have hh := signed_offsets_sum q
    rw [hqs,hf,hp] at hh
    norm_num only [Nat.cast_zero,Nat.cast_one,zero_sub] at hh
    exact hh
  have hbounds := (actual_sign_offset_bounds q hqm).1
  rw [hqe] at hbounds
  norm_num only [neg_zero,zero_sub,zero_add] at hbounds
  have hpair : LocalPairSignConstraints A.filling B.filling 1 0
      (positiveSignOffset q) (negativeSignOffset q) := by
    constructor
    · intro S T hS hT
      have hh := two_window_positive_selection A B q hqm hma hmb hab S T hS hT
      simpa only [hp,hqe,Nat.cast_one] using hh
    · intro S T hS hT
      have hh := two_window_negative_selection A B q hqm hma hmb hab S T hS hT
      simpa only [hp,hqe,Nat.cast_one] using hh
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
  have hforbid := odd_full_five_forbids_extra _ _ hmem' _ _ hsum hbounds.1 hbounds.2 hpair
  by_cases hs : 0 < displacement q.symm i
  · have hcst := actual_offset_extra_arrow_constraint A B q hqm hma hmb hab i hia hib
      1 (Or.inl rfl) (by simpa using hs)
    rw [hp,hqe] at hcst
    exact hforbid 1 _ (Or.inl rfl) hsmall hcst
  · have hcst := actual_offset_extra_arrow_constraint A B q hqm hma hmb hab i hia hib
      (-1) (Or.inr rfl) (by simp only [neg_one_mul]; omega)
    rw [hp,hqe] at hcst
    exact hforbid (-1) _ (Or.inr rfl) hsmall hcst

#print axioms odd_full_five_extra_arrow_check
#print axioms odd_full_five_forbids_extra
#print axioms actual_odd_full_width_five_large_min_arrow
end LRX.FiniteCuts

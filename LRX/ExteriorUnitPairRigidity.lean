module

public import LRX.ActualFilteredExteriorCatalogue

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords

def unitExteriorMap : SmallExteriorMap := ⟨2,Equiv.swap (0 : Fin 2) 1⟩

theorem fin_two_full_support_swap : ∀ σ : State 2,
    σ.support.card=2 → σ=Equiv.swap (0 : Fin 2) 1 := by
  decide +kernel

/-- Width four and full support force the two external maps to be unit pairs. -/
theorem filtered_full_support_width_four (A B : SmallExteriorMap) (parity eps : ℤ)
    (isolated : ℕ)
    (h : (A,B) ∈ filteredExteriorCatalogue parity eps 0 isolated 4) :
    isolated=0 ∧ A=unitExteriorMap ∧ B=unitExteriorMap := by
  obtain ⟨ha,hb,⟨hwidth,hfixed⟩,_⟩ := (filtered_catalogue_mem_iff A B parity eps 0 isolated 4).mp h
  have hAs := catalogue_member_size A ha
  have hBs := catalogue_member_size B hb
  rcases A with ⟨a,σ⟩
  rcases B with ⟨b,τ⟩
  dsimp only at hwidth hfixed hAs hBs ⊢
  have ha2 : a=2 := by omega
  have hb2 : b=2 := by omega
  subst a
  subst b
  have hσle : σ.support.card ≤ 2 := by simpa using Finset.card_le_univ σ.support
  have hτle : τ.support.card ≤ 2 := by simpa using Finset.card_le_univ τ.support
  have hσ := fin_two_full_support_swap σ (by omega)
  have hτ := fin_two_full_support_swap τ (by omega)
  subst σ
  subst τ
  exact ⟨by omega,rfl,rfl⟩

/-- The scalar full-support,width-four case yields genuine external unit pairs. -/
theorem actual_unpaid_external_unit_pairs {n k : ℕ} [NeZero n]
    (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (hf : n-p.support.card=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    ∃ A B : FillingWindow n, suffixComponentFamily q L=[A,B] ∧
      A.Matches q.symm ∧ B.Matches q.symm ∧ A.Apart B ∧
      (⟨A.size,A.filling⟩ : SmallExteriorMap)=unitExteriorMap ∧
      (⟨B.size,B.filling⟩ : SmallExteriorMap)=unitExteriorMap := by
  obtain ⟨A,B,hlist,hma,hmb,hab,hmem⟩ :=
    actual_unpaid_filtered_exterior_pair hn p hmaj hmax hc hk root hlarge ht hpos
  rw [hf,hv] at hmem
  obtain ⟨_,hA,hB⟩ := filtered_full_support_width_four _ _ _ _ _ hmem
  exact ⟨A,B,hlist,hma,hmb,hab,hA,hB⟩

#print axioms fin_two_full_support_swap
#print axioms filtered_full_support_width_four
#print axioms actual_unpaid_external_unit_pairs
end LRX.FiniteCuts

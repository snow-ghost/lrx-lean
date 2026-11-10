import LRX.ShallowGeometricDeficit

/-! M3, shallow shell with even root size: its two distinct rank-neighbor
arrows give a linear exterior reserve, without selecting a dominant gap. -/
namespace LRX.ContractionBlocks.System
open ZeroGap
open scoped BigOperators
variable {r n : ℕ}

theorem physical_mass_mod_two (P : State (r+1)) (f : Fin (r+1) → ℤ) :
    physicalMass P f%2=0 := by
  have hh := AffineLift.subset_displacement_balance (fun i => f (P i)-f i) Finset.univ
    (physical_displacement_balance P f)
  change physicalMass P f=2*_ at hh
  omega

theorem full_rank_neighbor_gap (a b : Fin (r+1))
    (h : RankAdjacent Finset.univ a b) :
    ∃ g : Fin r, (a=g.castSucc ∧ b=g.succ) ∨ (b=g.castSucc ∧ a=g.succ) := by
  have hu := FiniteCuts.full_carrier_neighbor_unit h
  have hav := a.isLt
  have hbv := b.isLt
  simp only [abs_eq_max_neg] at hu
  by_cases hab : a.val < b.val
  · let g : Fin r := ⟨a.val,by omega⟩
    exact ⟨g,Or.inl ⟨Fin.ext rfl,Fin.ext (by dsimp [g]; omega)⟩⟩
  · let g : Fin r := ⟨b.val,by omega⟩
    exact ⟨g,Or.inr ⟨Fin.ext rfl,Fin.ext (by dsimp [g]; omega)⟩⟩

theorem two_neighbor_length_sum (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    (a b x y : Fin (r+1)) (hab : RankAdjacent Finset.univ a b)
    (hxy : RankAdjacent Finset.univ x y)
    (hdiff : ¬((x=a ∧ y=b) ∨ (x=b ∧ y=a))) :
    |f b-f a|+|f y-f x| ≤ holeMass f+2 := by
  classical
  obtain ⟨g,hg⟩ := full_rank_neighbor_gap a b hab
  obtain ⟨j,hj⟩ := full_rank_neighbor_gap x y hxy
  have hgj : g ≠ j := by
    intro he
    subst j
    apply hdiff
    rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  let holes (i : Fin r) := f i.succ-f i.castSucc-1
  have hnon (i : Fin r) : 0 ≤ holes i := by
    have hh := hf (show i.castSucc < i.succ by change i.val < i.val+1; omega)
    dsimp [holes]; omega
  have hsum := Finset.single_le_sum (s := Finset.univ.erase j) (f := holes)
    (fun i _ => hnon i) (Finset.mem_erase.mpr ⟨hgj,Finset.mem_univ g⟩)
  have he := Finset.sum_erase_add Finset.univ holes (Finset.mem_univ j)
  have hglen : |f b-f a|=holes g+1 := by
    have hh := hnon g
    rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [abs_of_nonneg (by dsimp [holes] at hh; omega)]; dsimp [holes]; ring
    · rw [abs_sub_comm,abs_of_nonneg (by dsimp [holes] at hh; omega)]; dsimp [holes]; ring
  have hjlen : |f y-f x|=holes j+1 := by
    have hh := hnon j
    rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [abs_of_nonneg (by dsimp [holes] at hh; omega)]; dsimp [holes]; ring
    · rw [abs_sub_comm,abs_of_nonneg (by dsimp [holes] at hh; omega)]; dsimp [holes]; ring
  change _ ≤ (∑ i, holes i)+2
  omega

theorem no_extreme_arrow_of_wide (P : State (r+1)) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f) (h : ℤ)
    (hshort : ∀ i, |f (P i)-f i| ≤ h) (hhalf : 2*h < n)
    (hwide : (n : ℤ) ≤ 2*(f (Fin.last r)-f 0)) :
    ∀ x y, ExtremePair P.support x y → P x ≠ y := by
  intro x y hext hxy
  rw [hfull] at hext
  have hlo := (hext.2.2.2 0 (Finset.mem_univ _)).1
  have hhi := (hext.2.2.2 (Fin.last r) (Finset.mem_univ _)).2
  have hx := x.isLt
  have hy := y.isLt
  have hh := hshort x
  rw [hxy] at hh
  have hord := hf.monotone (Fin.zero_le (Fin.last r))
  have hcases : (x=0 ∧ y=Fin.last r) ∨ (y=0 ∧ x=Fin.last r) := by
    simp only [Fin.val_zero,Fin.val_last] at hlo hhi
    by_cases h : x.val ≤ y.val
    · left; constructor <;> apply Fin.ext <;> simp only [Fin.val_zero,Fin.val_last] <;> omega
    · right; constructor <;> apply Fin.ext <;> simp only [Fin.val_zero,Fin.val_last] <;> omega
  rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [abs_of_nonneg (by omega)] at hh; omega
  · rw [abs_sub_comm,abs_of_nonneg (by omega)] at hh; omega

/-- Two rank-neighbor arrows jointly consume the internal holes. With an
even root size, the remaining exterior positions force H >= outside-1. -/
theorem even_shallow_exterior_reserve (P : State (r+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i)
    (l c outside : ℕ) (hr : r+1=2*l) (hn : n=r+1+c+outside)
    (hholes : holeMass f=(c : ℤ))
    (hwide : (n : ℤ) ≤ 2*(f (Fin.last r)-f 0)) :
    (outside : ℤ)-1 ≤ shellDeficit n l P f := by
  classical
  let H := shellDeficit n l P f
  have hcount := source_signs_card P hfull
  have hl : 1 ≤ l := by omega
  have hposcap := AffineLift.original_selected_positive_residual hm emb
    (fun i => f (P i)-f i) hδ (physical_displacement_balance P f) ∅ (Finset.empty_subset _)
  have hnegcap := AffineLift.original_selected_negative_residual hd hm emb
    (fun i => f (P i)-f i) hδ (physical_displacement_balance P f) ∅ (Finset.empty_subset _)
  rw [positive_sources_physical P f hf] at hposcap
  rw [negative_sources_physical P f hf] at hnegcap
  simp only [Finset.sum_empty,mul_zero,Finset.sdiff_empty,zero_add] at hposcap hnegcap
  change physicalMass P f ≤ _ at hposcap hnegcap
  have hH : H=(l : ℤ)*(n-l)-physicalMass P f := rfl
  by_contra hbad
  change ¬(outside : ℤ)-1 ≤ H at hbad
  have small_count (a : ℕ) (hcap : physicalMass P f ≤ (a : ℤ)*(n-a)) : l ≤ a := by
    by_contra ha
    have ha' : (a : ℤ) ≤ (l : ℤ)-1 := by omega
    have hN : (2*l : ℤ) ≤ n := by omega
    have hprod := mul_nonneg (show 0 ≤ (l : ℤ)-a-1 by omega)
      (show 0 ≤ (n : ℤ)-l-a by omega)
    nlinarith
  have hpcount : (positiveSources P).card=l := by
    have ha := small_count _ hposcap
    have hb := small_count _ hnegcap
    omega
  have hncount : (negativeSources P).card=l := by omega
  have hbound (i : Fin (r+1)) : (n : ℤ)-2*l+1 ≤ H+2*|f (P i)-f i| := by
    have hne : P i ≠ i := Equiv.Perm.mem_support.mp (by rw [hfull]; exact Finset.mem_univ _)
    have hneval : (P i).val ≠ i.val := fun h => hne (Fin.ext h)
    by_cases hsign : i.val < (P i).val
    · have hsub : {i} ⊆ Finset.univ.filter (fun j => 0 < f (P j)-f j) := by
        rw [positive_sources_physical P f hf]
        simp only [Finset.singleton_subset_iff,positiveSources,Finset.mem_filter,Finset.mem_univ,true_and]
        exact hsign
      have hc := AffineLift.original_selected_positive_residual hm emb
        (fun j => f (P j)-f j) hδ (physical_displacement_balance P f) {i} hsub
      rw [Finset.card_sdiff_of_subset hsub,positive_sources_physical P f hf,hpcount] at hc
      simp only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_sub hl,Nat.cast_one] at hc
      change physicalMass P f ≤ _ at hc
      nlinarith
    · have hsub : {i} ⊆ Finset.univ.filter (fun j => f (P j)-f j < 0) := by
        rw [negative_sources_physical P f hf]
        simp only [Finset.singleton_subset_iff,negativeSources,Finset.mem_filter,Finset.mem_univ,true_and]
        omega
      have hc := AffineLift.original_selected_negative_residual hd hm emb
        (fun j => f (P j)-f j) hδ (physical_displacement_balance P f) {i} hsub
      rw [Finset.card_sdiff_of_subset hsub,negative_sources_physical P f hf,hncount] at hc
      simp only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_sub hl,Nat.cast_one] at hc
      change physicalMass P f ≤ _ at hc
      nlinarith
  have hshort := ambient_physical_short hd hm P f emb hδ
  have hno := no_extreme_arrow_of_wide P hfull f hf (((n : ℤ)-1)/2) hshort (by omega) hwide
  obtain ⟨a,b,x,y,hab,hpab,hxy,hpxy,hneq⟩ := shallow_cycle_two_rank_neighbors hp hs hno
  rw [hfull] at hab hxy
  have hsum := two_neighbor_length_sum f hf a b x y hab hxy hneq
  rw [hholes] at hsum
  have ha := hbound a
  have hx := hbound x
  rw [hpab] at ha
  rw [hpxy] at hx
  omega

#print axioms full_rank_neighbor_gap
#print axioms physical_mass_mod_two
#print axioms two_neighbor_length_sum
#print axioms no_extreme_arrow_of_wide
#print axioms even_shallow_exterior_reserve
end LRX.ContractionBlocks.System

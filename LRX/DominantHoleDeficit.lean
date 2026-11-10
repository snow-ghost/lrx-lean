import LRX.SelectedEnergyDeficit

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {r n : ℕ}

/-- The contraction branch of (30), including the nonnegative imbalance
terms, derived from actual protected selections and original majorization. -/
theorem dominant_hole_contracted_deficit (P : State (r+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i)
    (h : ℤ) (hshort : ∀ x, |f (P x)-f x| ≤ h) (hhalf : 2*h < n)
    (gap : Fin r) (l η t j s b c outside : ℕ)
    (hr : r+1=2*l+η) (hn : n=r+1+s) (hslots : s=b+c+outside)
    (hgap : f gap.succ-f gap.castSucc-1=b) (hholes : holeMass f=(b : ℤ)+c)
    (hpos : (positiveSources P).card=l+η+t) (hneg : (negativeSources P).card=l-t)
    (htj : t < j) (hthreshold : 2*(j : ℤ)+η ≤ 2*(b : ℤ)-s) :
    (j : ℤ)*(2*(b : ℤ)-s+2*outside-η-j)+2*t*(t+η)+2*t*c ≤ shellDeficit n l P f := by
  have hjt : t ≤ j := by omega
  have hmin : min (j+η+t) (j-t)=j-t := by omega
  obtain ⟨k,q,B,_,_,_,hselected⟩ := dominant_hole_selected_bound P hp hs hfull f hf h hshort
    gap n s (j+η+t) (j-t) hn hhalf (by omega) (by omega) (by
      rw [hgap]
      push_cast
      rw [Nat.cast_sub hjt]
      omega)
  rw [hmin,hholes,hgap] at hselected
  have hdef := B.selected_energy_deficit f hf hd hm emb hδ l η t j hpos hneg htj
    (((j+η+t : ℕ) : ℤ)*(j-t : ℕ)+(j-t : ℕ)*((b : ℤ)+c-b)) hselected
  simp only [Nat.cast_add,Nat.cast_sub hjt] at hdef
  have hnr : (n : ℤ)=2*l+η+s := by exact_mod_cast (show n=2*l+η+s by omega)
  have hslot : (s : ℤ)=b+c+outside := by exact_mod_cast hslots
  nlinarith

#print axioms dominant_hole_contracted_deficit

theorem dominant_hole_deficit (P : State (r+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i)
    (h : ℤ) (hshort : ∀ x, |f (P x)-f x| ≤ h) (hhalf : 2*h < n)
    (gap : Fin r) (l η t j s b c outside : ℕ)
    (hr : r+1=2*l+η) (hn : n=r+1+s) (hslots : s=b+c+outside)
    (hgap : f gap.succ-f gap.castSucc-1=b) (hholes : holeMass f=(b : ℤ)+c)
    (hpos : (positiveSources P).card=l+η+t) (hneg : (negativeSources P).card=l-t)
    (hthreshold : 2*(j : ℤ)+η ≤ 2*(b : ℤ)-s) :
    (j : ℤ)*(2*(b : ℤ)-s+2*outside-η-j) ≤ shellDeficit n l P f := by
  by_cases htj : t < j
  · have hc := dominant_hole_contracted_deficit P hp hs hfull f hf hd hm emb hδ h hshort hhalf
      gap l η t j s b c outside hr hn hslots hgap hholes hpos hneg htj hthreshold
    have h1 : (0 : ℤ) ≤ 2*t*(t+η) := by positivity
    have h2 : (0 : ℤ) ≤ 2*t*c := by positivity
    linarith
  · have hcard : (positiveSources P).card ≤ r+1 := by simpa using Finset.card_le_univ (positiveSources P)
    have htl : t ≤ l := by omega
    have hc := initial_negative_energy_deficit P f hf hd hm emb hδ l t htl hneg
    have hnr : (n : ℤ)=2*l+η+s := by exact_mod_cast (show n=2*l+η+s by omega)
    have hslot : (s : ℤ)=b+c+outside := by exact_mod_cast hslots
    have hprod := mul_nonneg (show (0 : ℤ) ≤ t-j by omega) (show (0 : ℤ) ≤ s+η by positivity)
    have htj' : (j : ℤ) ≤ t := by omega
    nlinarith

/-- Exact parity conversion used in the second inequality of (30). -/
theorem deficit_parity_conversion (H v η outside j : ℤ)
    (hj : j=(v-η)/2) (hH : j*(v+2*outside-η-j) ≤ H) :
    (v-η)^2-(v-η)%2+8*j*outside ≤ 4*H := by
  have hr0 := Int.emod_nonneg (v-η) (by norm_num : (2 : ℤ) ≠ 0)
  have hr2 := Int.emod_lt_of_pos (v-η) (by norm_num : (0 : ℤ) < 2)
  have he := Int.ediv_mul_add_emod (v-η) 2
  have hp : (v-η)%2=0 ∨ (v-η)%2=1 := by omega
  rcases hp with hp | hp <;> rw [hp] at he ⊢ <;> rw [← hj] at he <;> nlinarith

#print axioms dominant_hole_deficit
#print axioms deficit_parity_conversion
theorem dominant_hole_quadratic_deficit (P : State (r+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i)
    (h : ℤ) (hshort : ∀ x, |f (P x)-f x| ≤ h) (hhalf : 2*h < n)
    (gap : Fin r) (l η t j s b c outside : ℕ)
    (hr : r+1=2*l+η) (hn : n=r+1+s) (hslots : s=b+c+outside)
    (hgap : f gap.succ-f gap.castSucc-1=b) (hholes : holeMass f=(b : ℤ)+c)
    (hpos : (positiveSources P).card=l+η+t) (hneg : (negativeSources P).card=l-t)
    (hj : (j : ℤ)=(2*(b : ℤ)-s-η)/2) :
    (2*(b : ℤ)-s-η)^2-(2*(b : ℤ)-s-η)%2+8*j*outside ≤ 4*shellDeficit n l P f := by
  have ht : 2*(j : ℤ)+η ≤ 2*(b : ℤ)-s := by omega
  have hh := dominant_hole_deficit P hp hs hfull f hf hd hm emb hδ h hshort hhalf
    gap l η t j s b c outside hr hn hslots hgap hholes hpos hneg ht
  exact deficit_parity_conversion (shellDeficit n l P f) (2*(b : ℤ)-s) η outside j hj hh

#print axioms dominant_hole_quadratic_deficit
end LRX.ContractionBlocks.System

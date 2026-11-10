module

public import LRX.DominantHoleDeficit

@[expose] public section

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {r n : ℕ}

theorem exterior_hole_contracted_deficit (P : State (r+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i)
    (l η t j s c outside : ℕ) (hr : r+1=2*l+η) (hn : n=r+1+s)
    (hslots : s=c+outside) (hholes : holeMass f=c)
    (hpos : (positiveSources P).card=l+η+t) (hneg : (negativeSources P).card=l-t)
    (htj : t < j) (hsize : 2*j+η < r+1) :
    (j : ℤ)*((outside : ℤ)-c-η-j)+2*t*(t+η)+2*t*c ≤ shellDeficit n l P f := by
  have hjt : t ≤ j := by omega
  have hmin : min (j+η+t) (j-t)=j-t := by omega
  obtain ⟨k,q,B,_,_,hselected⟩ := shallow_selected_physical_bound P hp hs hfull f hf
    (j+η+t) (j-t) (by omega) (by omega) (by omega)
  rw [hmin,hholes] at hselected
  have hdef := B.selected_energy_deficit f hf hd hm emb hδ l η t j hpos hneg htj
    (((j+η+t : ℕ) : ℤ)*(j-t : ℕ)+(j-t : ℕ)*c) hselected
  simp only [Nat.cast_add,Nat.cast_sub hjt] at hdef
  have hnr : (n : ℤ)=2*l+η+s := by exact_mod_cast (show n=2*l+η+s by omega)
  have hslot : (s : ℤ)=c+outside := by exact_mod_cast hslots
  nlinarith

theorem exterior_hole_deficit (P : State (r+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i)
    (l η t j s c outside : ℕ) (hr : r+1=2*l+η) (hn : n=r+1+s)
    (hslots : s=c+outside) (hholes : holeMass f=c)
    (hpos : (positiveSources P).card=l+η+t) (hneg : (negativeSources P).card=l-t)
    (hsize : 2*j+η < r+1) :
    (j : ℤ)*((outside : ℤ)-c-η-j) ≤ shellDeficit n l P f := by
  by_cases htj : t < j
  · have hc := exterior_hole_contracted_deficit P hp hs hfull f hf hd hm emb hδ
      l η t j s c outside hr hn hslots hholes hpos hneg htj hsize
    have h1 : (0 : ℤ) ≤ 2*t*(t+η) := by positivity
    have h2 : (0 : ℤ) ≤ 2*t*c := by positivity
    linarith
  · have hcard : (positiveSources P).card ≤ r+1 := by simpa using Finset.card_le_univ (positiveSources P)
    have htl : t ≤ l := by omega
    have hc := initial_negative_energy_deficit P f hf hd hm emb hδ l t htl hneg
    have hnr : (n : ℤ)=2*l+η+s := by exact_mod_cast (show n=2*l+η+s by omega)
    have hslot : (s : ℤ)=c+outside := by exact_mod_cast hslots
    have hprod := mul_nonneg (show (0 : ℤ) ≤ t-j by omega) (show (0 : ℤ) ≤ s+η by positivity)
    have htj' : (j : ℤ) ≤ t := by omega
    nlinarith

theorem deficit_floor_square (H v η j : ℤ) (hj : j=(v-η)/2)
    (hH : j*(v-η-j) ≤ H) : (v-η)^2/4 ≤ H := by
  have hh := deficit_parity_conversion H v η 0 j hj (by simpa using hH)
  have hr := Int.emod_lt_of_pos (v-η) (by norm_num : (0 : ℤ) < 2)
  simp only [mul_zero,add_zero] at hh
  omega

#print axioms exterior_hole_deficit
#print axioms deficit_floor_square
theorem exterior_hole_quadratic_deficit (P : State (r+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i)
    (l η t j s c outside : ℕ) (hr : r+1=2*l+η) (hn : n=r+1+s)
    (hslots : s=c+outside) (hholes : holeMass f=c)
    (hpos : (positiveSources P).card=l+η+t) (hneg : (negativeSources P).card=l-t)
    (hsize : 2*j+η < r+1) (hj : (j : ℤ)=((outside : ℤ)-c-η)/2) :
    ((outside : ℤ)-c-η)^2/4 ≤ shellDeficit n l P f := by
  have hh := exterior_hole_deficit P hp hs hfull f hf hd hm emb hδ
    l η t j s c outside hr hn hslots hholes hpos hneg hsize
  exact deficit_floor_square (shellDeficit n l P f) ((outside : ℤ)-c) η j hj hh

#print axioms exterior_hole_quadratic_deficit
end LRX.ContractionBlocks.System

import LRX.PhysicalSelectedCapacity

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {r k n : ℕ} {P : State (r+1)} {q : State k}

def shellDeficit (n l : ℕ) (P : State (r+1)) (f : Fin (r+1) → ℤ) : ℤ :=
  (l : ℤ)*(n-l)-physicalMass P f

/-- At the first threshold the attained sign has exactly l-j remaining
original arrows. Applying their ambient capacity gives the deficit bound. -/
theorem selected_energy_deficit (B : System P q) (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (e : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (e i)=f (P i)-f i)
    (l η t j : ℕ) (hpos : (positiveSources P).card=l+η+t)
    (hneg : (negativeSources P).card=l-t) (htj : t < j) (L : ℤ)
    (hselected : (B.positive.card=j+η+t ∧ physicalLength B.positive P f ≤ L) ∨
      (B.negative.card=j-t ∧ physicalLength B.negative P f ≤ L)) :
    (j : ℤ)*((n : ℤ)-2*l+j)-2*L ≤ shellDeficit n l P f := by
  unfold shellDeficit
  rcases hselected with h | h
  · have hs := Finset.card_le_card B.positive_subset_sources
    have hjl : j ≤ l := by omega
    have hrem : (positiveSources P).card-B.positive.card=l-j := by omega
    have hc := B.positive_remaining_capacity f hf hm e hδ
    rw [hrem,Nat.cast_sub hjl] at hc
    nlinarith [h.2]
  · have hs := Finset.card_le_card B.negative_subset_sources
    have hjl : j ≤ l := by omega
    have hrem : (negativeSources P).card-B.negative.card=l-j := by omega
    have hc := B.negative_remaining_capacity f hf hd hm e hδ
    rw [hrem,Nat.cast_sub hjl] at hc
    nlinarith [h.2]

/-- The starting sign-capacity bound, used when no contractions are needed. -/
theorem initial_negative_energy_deficit (P : State (r+1)) (f : Fin (r+1) → ℤ)
    (hf : StrictMono f) {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (e : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (e i)=f (P i)-f i)
    (l t : ℕ) (htl : t ≤ l) (hneg : (negativeSources P).card=l-t) :
    (t : ℤ)*((n : ℤ)-2*l+t) ≤ shellDeficit n l P f := by
  have hc := AffineLift.original_selected_negative_residual hd hm e
    (fun i => f (P i)-f i) hδ (physical_displacement_balance P f) ∅ (Finset.empty_subset _)
  rw [negative_sources_physical P f hf] at hc
  simp only [Finset.sum_empty,mul_zero,Finset.sdiff_empty,zero_add,hneg,Nat.cast_sub htl] at hc
  change physicalMass P f ≤ ((l : ℤ)-t)*(n-((l : ℤ)-t)) at hc
  unfold shellDeficit
  nlinarith

#print axioms selected_energy_deficit
#print axioms initial_negative_energy_deficit
end LRX.ContractionBlocks.System

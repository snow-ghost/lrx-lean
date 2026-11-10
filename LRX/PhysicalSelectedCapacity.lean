import LRX.SelectedMajorization

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {r k n : ℕ} {P : State r} {q : State k}

def positiveSources (P : State r) : Finset (Fin r) := Finset.univ.filter (fun x => x.val < (P x).val)
def negativeSources (P : State r) : Finset (Fin r) := Finset.univ.filter (fun x => (P x).val < x.val)
def physicalMass (P : State r) (f : Fin r → ℤ) : ℤ := ∑ x, |f (P x)-f x|

theorem physical_displacement_balance (P : State r) (f : Fin r → ℤ) :
    (∑ x, (f (P x)-f x))=0 := by
  rw [Finset.sum_sub_distrib,Equiv.sum_comp P f,sub_self]

theorem positive_sources_physical (P : State r) (f : Fin r → ℤ) (hf : StrictMono f) :
    Finset.univ.filter (fun x => 0 < f (P x)-f x)=positiveSources P := by
  ext x
  simp only [positiveSources,Finset.mem_filter,Finset.mem_univ,true_and,sub_pos,hf.lt_iff_lt]
  rfl

theorem negative_sources_physical (P : State r) (f : Fin r → ℤ) (hf : StrictMono f) :
    Finset.univ.filter (fun x => f (P x)-f x < 0)=negativeSources P := by
  ext x
  simp only [negativeSources,Finset.mem_filter,Finset.mem_univ,true_and,sub_neg,hf.lt_iff_lt]
  rfl

theorem positive_subset_sources (B : System P q) : B.positive ⊆ positiveSources P := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩

theorem negative_subset_sources (B : System P q) : B.negative ⊆ negativeSources P := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩

theorem positive_remaining_capacity {r : ℕ} {P : State (r+1)} {q : State k}
    (B : System P q) (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hm : AffineLift.Majorized d) (e : Fin (r+1) ↪ Fin n)
    (hδ : ∀ i, d (e i)=f (P i)-f i) :
    physicalMass P f ≤ 2*physicalLength B.positive P f+
      (((positiveSources P).card-B.positive.card : ℕ) : ℤ)*
        (n-((positiveSources P).card-B.positive.card : ℕ)) := by
  have hc := AffineLift.original_selected_positive_residual hm e
    (fun i => f (P i)-f i) hδ (physical_displacement_balance P f) B.positive (by
      rw [positive_sources_physical P f hf]
      exact B.positive_subset_sources)
  rw [positive_sources_physical P f hf,
    Finset.card_sdiff_of_subset B.positive_subset_sources] at hc
  exact hc

theorem negative_remaining_capacity {r : ℕ} {P : State (r+1)} {q : State k}
    (B : System P q) (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (e : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (e i)=f (P i)-f i) :
    physicalMass P f ≤ 2*physicalLength B.negative P f+
      (((negativeSources P).card-B.negative.card : ℕ) : ℤ)*
        (n-((negativeSources P).card-B.negative.card : ℕ)) := by
  have hc := AffineLift.original_selected_negative_residual hd hm e
    (fun i => f (P i)-f i) hδ (physical_displacement_balance P f) B.negative (by
      rw [negative_sources_physical P f hf]
      exact B.negative_subset_sources)
  rw [negative_sources_physical P f hf,
    Finset.card_sdiff_of_subset B.negative_subset_sources] at hc
  exact hc

#print axioms positive_remaining_capacity
#print axioms negative_remaining_capacity
end LRX.ContractionBlocks.System

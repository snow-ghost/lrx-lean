import LRX.PrefixCoreEnergy

namespace LRX.FiniteWindow
open FiniteCuts
variable {n b : ℕ}

theorem matched_window_half_load_le (W : Window n b) (p : State n) (f : State b)
    (hm : ∀ i, p (embed W i)=embed W (f i)) (e : ℕ) :
    halfLoad f e ≤ halfLoad p (W.offset+e) := by
  classical
  unfold halfLoad
  rw [← Finset.card_image_of_injective (forward f e) (embed_injective W)]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hil,hih⟩ := (mem_forward f e i).mp hi
  apply (mem_forward p _ _).mpr
  rw [hm]
  dsimp only [embed]
  omega

theorem matched_window_peak_le (W : Window n b) (p : State n) (f : State b)
    (hm : ∀ i, p (embed W i)=embed W (f i)) : leftPeak f b ≤ leftPeak p n := by
  apply Finset.sup_le
  intro e he
  have heB := Finset.mem_range.mp he
  have hfits := W.fits
  have heN : W.offset+e ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
  exact (matched_window_half_load_le W p f hm e).trans (Finset.le_sup heN)

#print axioms matched_window_peak_le
end LRX.FiniteWindow

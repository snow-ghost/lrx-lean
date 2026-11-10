module

public import LRX.ShallowContractionTrace
public import LRX.ContractionSelectedCapacity

@[expose] public section

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {m k : ℕ} {P : State m} {q : State k}

def rankLength (S : Finset (Fin m)) (P : State m) : ℤ :=
  ∑ x ∈ S, |(P x : ℤ)-(x : ℤ)|

theorem positive_rank_capacity (B : System P q) :
    rankLength B.positive P ≤ (B.positive.card : ℤ)*(B.negative.card+1) := by
  have hsub : B.positive ⊆ B.selected := Finset.filter_subset _ _
  have hc := B.selected_difference_capacity B.positive hsub
  have hs := B.signs_card
  have hsel := B.selected_card
  have hrest : (B.selected \ B.positive).card=B.negative.card := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  rw [hrest] at hc
  have he : rankLength B.positive P=∑ x ∈ B.positive, ((P x : ℤ)-(x : ℤ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    exact abs_of_nonneg (by omega)
  rwa [he]

theorem negative_rank_capacity (B : System P q) :
    rankLength B.negative P ≤ (B.negative.card : ℤ)*(B.positive.card+1) := by
  have hsub : B.negative ⊆ B.selected := Finset.filter_subset _ _
  have hc := B.selected_reverse_difference_capacity B.negative hsub
  have hs := B.signs_card
  have hsel := B.selected_card
  have hrest : (B.selected \ B.negative).card=B.positive.card := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  rw [hrest] at hc
  have he : rankLength B.negative P=∑ x ∈ B.negative, ((x : ℤ)-(P x : ℤ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    rw [abs_of_nonpos (by omega)]
    ring
  rwa [he]

end LRX.ContractionBlocks.System

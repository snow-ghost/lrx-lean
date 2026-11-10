module

public import LRX.PacketExchangeReserve

@[expose] public section

namespace LRX.FiniteGaps
variable {n : ℕ} [NeZero n]

theorem next_zero_of_consecutive (S : Finset (Fin n)) (r : Fin n) (hr : r ∈ S)
    (hpos : 0 < r.val) (hgap : ∀ i ∈ S, 0 < i.val → r.val ≤ i.val) :
    next S 0=r.val := by
  have hle := next_le_member S 0 r hr (by simpa using hpos)
  have hnext : next S 0<n := lt_of_le_of_lt hle r.isLt
  obtain ⟨i,hi,he⟩ := next_is_member S 0 hnext
  have hgt := lt_next S (0 : Fin n)
  have hge := hgap i hi (by simp only [Fin.val_zero] at hgt; omega)
  omega

end LRX.FiniteGaps

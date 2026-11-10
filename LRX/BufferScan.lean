import LRX.BufferFrame
import LRX.PeriodicBuffer

/-! The motion scanner visits contracted ports at both ends as well as in the
interior. The splitting theorem is an equality of actual command lists. -/
namespace LRX.BufferProgram
variable {n : ℕ}

theorem move_nonneg {d : ℤ} (hd : 0 ≤ d) :
    move (n := n) d=List.replicate d.natAbs .forward := by
  simp [move, hd]

theorem move_nonpos {d : ℤ} (hd : d ≤ 0) :
    move (n := n) d=List.replicate d.natAbs .backward := by
  by_cases hz : d=0
  · subst d; simp [move]
  · simp [move, show ¬ 0 ≤ d by omega]

/-- Every intermediate signed displacement determines a literal prefix and
suffix, including displacement zero and the endpoint displacement. -/
theorem move_split (d a : ℤ) (ha : min 0 d ≤ a) (hb : a ≤ max 0 d) :
    move (n := n) d=move a ++ move (d-a) := by
  by_cases hd : 0 ≤ d
  · have ha0 : 0 ≤ a := by simpa only [min_eq_left hd] using ha
    have had : a ≤ d := by simpa only [max_eq_right hd] using hb
    have hr : 0 ≤ d-a := by omega
    have hlen : d.natAbs=a.natAbs+(d-a).natAbs := by
      have h1 := Int.natCast_natAbs d
      have h2 := Int.natCast_natAbs a
      have h3 := Int.natCast_natAbs (d-a)
      rw [abs_of_nonneg hd] at h1
      rw [abs_of_nonneg ha0] at h2
      rw [abs_of_nonneg hr] at h3
      omega
    rw [move_nonneg hd, move_nonneg ha0, move_nonneg hr, hlen, List.replicate_add]
  · have hd0 : d ≤ 0 := by omega
    have ha0 : a ≤ 0 := by simpa only [max_eq_left hd0] using hb
    have hda : d ≤ a := by simpa only [min_eq_right hd0] using ha
    have hr : d-a ≤ 0 := by omega
    have hlen : d.natAbs=a.natAbs+(d-a).natAbs := by
      have h1 := Int.natCast_natAbs d
      have h2 := Int.natCast_natAbs a
      have h3 := Int.natCast_natAbs (d-a)
      rw [abs_of_nonpos hd0] at h1
      rw [abs_of_nonpos ha0] at h2
      rw [abs_of_nonpos hr] at h3
      omega
    rw [move_nonpos hd0, move_nonpos ha0, move_nonpos hr, hlen, List.replicate_add]

theorem contracted_between {N : ℤ} (hN : 0 < N) (a b v : ℤ)
    (hv : min a b ≤ v ∧ v ≤ max a b) :
    min 0 (PeriodicBuffer.contract N b-PeriodicBuffer.contract N a) ≤
      PeriodicBuffer.contract N v-PeriodicBuffer.contract N a ∧
    PeriodicBuffer.contract N v-PeriodicBuffer.contract N a ≤
      max 0 (PeriodicBuffer.contract N b-PeriodicBuffer.contract N a) := by
  have hf := PeriodicBuffer.contract_monotone hN
  rcases le_total a b with hab | hba
  · have ha : a ≤ v := by simpa only [min_eq_left hab] using hv.1
    have hb : v ≤ b := by simpa only [max_eq_right hab] using hv.2
    have h1 := hf ha
    have h2 := hf hb
    omega
  · have hb : b ≤ v := by simpa only [min_eq_right hba] using hv.1
    have ha : v ≤ a := by simpa only [max_eq_left hba] using hv.2
    have h1 := hf hb
    have h2 := hf ha
    omega

#print axioms move_split
end LRX.BufferProgram

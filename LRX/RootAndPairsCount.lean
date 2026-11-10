import LRX.TranspositionPeak
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- For one distinguished cycle and only transpositions outside it, both
the number of remaining services and their total half-peak are exact. -/
theorem root_and_pairs_count (G C : State n)
    (hC : C ∈ G.cycleFactorsFinset)
    (hpairs : ∀ D ∈ G.cycleFactorsFinset, D ≠ C →
      ∃ a b : Fin n, a ≠ b ∧ D=Equiv.swap a b) :
    C.support.card+2*(G.cycleFactorsFinset.erase C).card=G.support.card ∧
    (∑ D ∈ G.cycleFactorsFinset.erase C, leftPeak D n)=
      (G.cycleFactorsFinset.erase C).card := by
  classical
  have hcard (D : State n) (hD : D ∈ G.cycleFactorsFinset.erase C) : D.support.card=2 := by
    obtain ⟨a,b,hab,rfl⟩ := hpairs D (Finset.mem_erase.mp hD).2 (Finset.mem_erase.mp hD).1
    simp only [Equiv.Perm.support_swap hab,Finset.card_pair hab]
  have hsum : (∑ D ∈ G.cycleFactorsFinset, D.support.card)=G.support.card := by
    simpa only [Equiv.Perm.cycleType_def,Function.comp_def,Finset.sum] using G.sum_cycleType
  have hsplit := Finset.sum_erase_add G.cycleFactorsFinset (fun D => D.support.card) hC
  have hrest : (∑ D ∈ G.cycleFactorsFinset.erase C, D.support.card)=
      2*(G.cycleFactorsFinset.erase C).card := by
    calc
      _ = ∑ _D ∈ G.cycleFactorsFinset.erase C, 2 := Finset.sum_congr rfl hcard
      _ = _ := by simp [Nat.mul_comm]
  constructor
  · omega
  · calc
      _ = ∑ _D ∈ G.cycleFactorsFinset.erase C, 1 := by
        apply Finset.sum_congr rfl
        intro D hD
        obtain ⟨a,b,hab,rfl⟩ := hpairs D (Finset.mem_erase.mp hD).2 (Finset.mem_erase.mp hD).1
        exact transposition_left_peak a b hab
      _ = _ := by simp

#print axioms root_and_pairs_count
end LRX.FiniteCuts

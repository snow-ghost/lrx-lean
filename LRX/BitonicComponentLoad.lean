import LRX.EventComponentCycleBudget
import LRX.FiniteCycleLoads

namespace LRX.ZeroGap
open FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Arrows starting in a graph component are charged only to its own
cycles; a unit cycle peak allows at most one charge at the cut. -/
theorem component_forward_le_cycle_count (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) (root : Fin n) (cut : ℕ) (hcut : cut ≤ n)
    (hpeak : ∀ c ∈ p.cycleFactorsFinset, leftPeak c n ≤ 1) :
    (forward p cut ∩ eventComponent events root).card ≤ (componentCycles events p root).card := by
  classical
  let cycles := componentCycles events p root
  have hsub : forward p cut ∩ eventComponent events root ⊆
      cycles.biUnion (fun c => forward c cut) := by
    intro i hi
    obtain ⟨hforward,hir⟩ := Finset.mem_inter.mp hi
    have hm : i ∈ p.support := by
      apply Equiv.Perm.mem_support.mpr
      intro hh
      have h := (mem_forward p cut i).mp hforward
      rw [hh] at h
      omega
    obtain ⟨c,hc,hic⟩ := Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hm
    have hci : c ∈ cycles := Finset.mem_filter.mpr
      ⟨hc,cycle_support_in_component events p hprod root c hc i hic hir⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨c,hci,?_⟩
    have he := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 i hic
    apply (mem_forward c cut i).mpr
    rw [he]
    exact (mem_forward p cut i).mp hforward
  calc
    _ ≤ (cycles.biUnion (fun c => forward c cut)).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ cycles, (forward c cut).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ cycles, 1 := by
      apply Finset.sum_le_sum
      intro c hc
      have hp := hpeak c (Finset.mem_filter.mp hc).1
      have hl : halfLoad c cut ≤ leftPeak c n :=
        Finset.le_sup (Finset.mem_range.mpr (by omega))
      change halfLoad c cut ≤ 1
      omega
    _ = _ := by simp [cycles]

/-- The first three vertices of a physical interval all cross one cut
when its permutation arrows have length at least three. -/
theorem nonshort_interval_three_cycles (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) (root : Fin n)
    (hint : CarrierInterval (eventComponent events root) Finset.univ)
    (hmin : ∀ i ∈ eventComponent events root, 3 ≤ |displacement p i|)
    (hpeak : ∀ c ∈ p.cycleFactorsFinset, leftPeak c n ≤ 1) :
    3 ≤ (componentCycles events p root).card := by
  classical
  let C := eventComponent events root
  have hroot : root ∈ C := (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
  let a := C.min' ⟨root,hroot⟩
  have ha : a ∈ C := Finset.min'_mem _ _
  have hclosed (i : Fin n) (hi : i ∈ C) : p i ∈ C := by
    apply (mem_eventComponent _ _ _).mpr
    have hh := event_product_reaches events events (fun _ h => h) i
    rw [hprod] at hh
    exact ((mem_eventComponent _ _ _).mp hi).trans hh
  have hlow (i : Fin n) (hi : i ∈ C) : a.val ≤ i.val := Finset.min'_le _ _ hi
  have hpa := hclosed a ha
  have hpaLow := hlow (p a) hpa
  have hpaLong := hmin a ha
  unfold displacement at hpaLong
  have hpaHigh : a.val+3 ≤ (p a).val := by
    rw [abs_of_nonneg (by omega)] at hpaLong
    omega
  have hn : a.val+3 < n := lt_of_le_of_lt hpaHigh (p a).isLt
  let b : Fin n := ⟨a.val+1,by omega⟩
  let c : Fin n := ⟨a.val+2,by omega⟩
  have hb : b ∈ C := hint.2 a ha (p a) hpa b (Finset.mem_univ _) (by dsimp [b]; omega) (by dsimp [b]; omega)
  have hc : c ∈ C := hint.2 a ha (p a) hpa c (Finset.mem_univ _) (by dsimp [c]; omega) (by dsimp [c]; omega)
  have hf (i : Fin n) (hi : i ∈ C) (hsmall : i.val ≤ a.val+2) : i ∈ forward p (a.val+3) := by
    have hpLow := hlow (p i) (hclosed i hi)
    have hlong := hmin i hi
    unfold displacement at hlong
    have hpHigh : a.val+3 ≤ (p i).val := by
      rw [abs_eq_max_neg] at hlong
      have hiLow := hlow i hi
      omega
    exact (mem_forward p _ i).mpr ⟨by omega,hpHigh⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [b] at this; omega
  have hac : a ≠ c := by intro h; have := congrArg Fin.val h; dsimp [c] at this; omega
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b,c] at this; omega
  have hthree : ({a,b,c} : Finset (Fin n)).card=3 := by simp [hab,hac,hbc]
  have hsub : ({a,b,c} : Finset (Fin n)) ⊆ forward p (a.val+3) ∩ C := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hf a ha (by omega),ha⟩
    · exact Finset.mem_inter.mpr ⟨hf b hb (by dsimp [b]; omega),hb⟩
    · exact Finset.mem_inter.mpr ⟨hf c hc (by dsimp [c]; omega),hc⟩
  have hh := (Finset.card_le_card hsub).trans
    (component_forward_le_cycle_count events p hprod root (a.val+3) (by omega) hpeak)
  rw [hthree] at hh
  exact hh

#print axioms component_forward_le_cycle_count
#print axioms nonshort_interval_three_cycles
end LRX.ZeroGap

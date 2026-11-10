import LRX.ExternalPairCycleJoin
import LRX.GlobalPeakServiceFamily

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Joining a pair strictly to the right of a cyclic core preserves its
global half-peak. Cuts inside the core are unchanged; later cuts have
half-load at most one. No majorization assumption on the upper map is used. -/
theorem external_pair_join_left_peak (A : State n) (hA : A.IsCycle)
    (u v z : Fin n) (hu : u ∈ A.support)
    (hmax : ∀ i ∈ A.support, i.val ≤ u.val)
    (huv : u.val < v.val) (hvz : v.val < z.val) :
    leftPeak (A*Equiv.swap v z*Equiv.swap u v) n=leftPeak A n := by
  classical
  let C := A*Equiv.swap v z*Equiv.swap u v
  have huvne : u ≠ v := fun h => by have := congrArg Fin.val h; omega
  have huzne : u ≠ z := fun h => by have := congrArg Fin.val h; omega
  have hvzne : v ≠ z := fun h => by have := congrArg Fin.val h; omega
  have hvfix : A v=v := Equiv.Perm.notMem_support.mp (by intro h; have := hmax v h; omega)
  have hzfix : A z=z := Equiv.Perm.notMem_support.mp (by intro h; have := hmax z h; omega)
  have hAu : (A u).val ≤ u.val := hmax _ (Equiv.Perm.apply_mem_support.mpr hu)
  have hCv : C v=A u := by
    simp only [C,Equiv.Perm.mul_apply,Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne huvne huzne]
  have hCz : C z=v := by
    simp only [C,Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm huzne) (Ne.symm hvzne),
      Equiv.swap_apply_right,hvfix]
  have hother (i : Fin n) (hiu : i ≠ u) (hiv : i ≠ v) (hiz : i ≠ z) : C i=A i := by
    simp only [C,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hiu hiv,
      Equiv.swap_apply_of_ne_of_ne hiv hiz]
  have hsmall (e : ℕ) (he : e ≤ u.val) : halfLoad C e=halfLoad A e := by
    change (forward C e).card=(forward A e).card
    congr 1
    ext i
    simp only [mem_forward]
    by_cases hi : i.val < e
    · have hiu : i ≠ u := fun h => by have := congrArg Fin.val h; omega
      have hiv : i ≠ v := fun h => by have := congrArg Fin.val h; omega
      have hiz : i ≠ z := fun h => by have := congrArg Fin.val h; omega
      rw [hother i hiu hiv hiz]
    · simp only [hi,false_and]
  have hlate_image (e : ℕ) (he : u.val < e) (i : Fin n) (hi : i.val < e) :
      (A i).val < e := by
    by_cases hm : i ∈ A.support
    · have hh := hmax _ (Equiv.Perm.apply_mem_support.mpr hm)
      omega
    · rwa [Equiv.Perm.notMem_support.mp hm]
  have hlate_zero (e : ℕ) (he : u.val < e) : halfLoad A e=0 := by
    have hempty : forward A e=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hl,hr⟩ := (mem_forward A e i).mp hi
      have hh := hlate_image e he i hl
      omega
    simp only [halfLoad,hempty,Finset.card_empty]
  have hlate_one (e : ℕ) (he : u.val < e) : halfLoad C e ≤ 1 := by
    have hsub : forward C e ⊆ {u} := by
      intro i hi
      obtain ⟨hl,hr⟩ := (mem_forward C e i).mp hi
      by_cases hiu : i=u
      · simpa only [Finset.mem_singleton] using hiu
      · by_cases hiv : i=v
        · subst i
          rw [hCv] at hr
          omega
        · by_cases hiz : i=z
          · subst i
            rw [hCz] at hr
            omega
          · rw [hother i hiu hiv hiz] at hr
            have hh := hlate_image e he i hl
            omega
    simpa only [halfLoad,Finset.card_singleton] using Finset.card_le_card hsub
  have hpositive := cycle_global_peak_positive A hA
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro e he
    by_cases hsmallcut : e ≤ u.val
    · rw [hsmall e hsmallcut]
      exact Finset.le_sup he
    · exact (hlate_one e (by omega)).trans (by omega)
  · apply Finset.sup_le
    intro e he
    by_cases hsmallcut : e ≤ u.val
    · rw [← hsmall e hsmallcut]
      exact Finset.le_sup he
    · rw [hlate_zero e (by omega)]
      exact Nat.zero_le _

#print axioms external_pair_join_left_peak
end LRX.FiniteCuts

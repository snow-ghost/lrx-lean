import LRX.ShallowShellBoundaryData
import LRX.ExternalPairCycleJoin

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ}

/-- Every position covered by genuinely reversed windows is an involutive
position of the upper map, irrespective of the original window filling. -/
theorem reversed_family_apply_apply (As : List (FillingWindow n)) (Q : State n)
    (hrev : ∀ B ∈ As, ∀ i,
      Q (embed B.window i)=embed B.window (Fin.revPerm i))
    (x : Fin n) (hx : x ∈ familyPositions As) : Q (Q x)=x := by
  obtain ⟨B,hB,hxB⟩ := (mem_family_positions As x).mp hx
  obtain ⟨i,rfl⟩ := (contains_iff B.window x).mp hxB
  rw [hrev B hB i,hrev B hB (Fin.revPerm i)]
  simp

/-- Once a boundary exchange has joined the chosen root, every other cycle
is a real transposition: its positions remain inside reversed windows. -/
theorem nonroot_cycle_swap_of_reversed_cover (As : List (FillingWindow n))
    (Q C : State n) (u v : Fin n)
    (hrev : ∀ B ∈ As, ∀ i,
      Q (embed B.window i)=embed B.window (Fin.revPerm i))
    (hC : C ∈ (Q*Equiv.swap u v).cycleFactorsFinset)
    (hu : u ∈ C.support) (hv : v ∈ C.support)
    (hcover : ∀ x, x ∉ C.support → x ∈ familyPositions As)
    (D : State n) (hD : D ∈ (Q*Equiv.swap u v).cycleFactorsFinset)
    (hne : D ≠ C) : ∃ a b : Fin n, a ≠ b ∧ D=Equiv.swap a b := by
  classical
  obtain ⟨hcycle,hact⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hD
  have hdis := (Q*Equiv.swap u v).cycleFactorsFinset_pairwise_disjoint hD hC hne
  have hout (x : Fin n) (hx : x ∈ D.support) : x ∉ C.support := by
    rcases hdis x with hd | hc
    · exact False.elim ((Equiv.Perm.mem_support.mp hx) hd)
    · exact Equiv.Perm.notMem_support.mpr hc
  have hQ (x : Fin n) (hx : x ∈ D.support) : Q x=D x := by
    have hxu : x ≠ u := fun he => hout x hx (he ▸ hu)
    have hxv : x ≠ v := fun he => hout x hx (he ▸ hv)
    simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hxu hxv] using
      (hact x hx).symm
  have hcycle' := hcycle
  obtain ⟨x,hx,_⟩ := hcycle'
  have hxmem : x ∈ D.support := Equiv.Perm.mem_support.mpr hx
  have hDxmem : D x ∈ D.support := Equiv.Perm.apply_mem_support.mpr hxmem
  have hdouble := reversed_family_apply_apply As Q hrev x (hcover x (hout x hxmem))
  rw [hQ x hxmem,hQ (D x) hDxmem] at hdouble
  exact ⟨x,D x,Ne.symm hx,hcycle.eq_swap_of_apply_apply_eq_self hx hdouble⟩

#print axioms nonroot_cycle_swap_of_reversed_cover
end LRX.FiniteCuts

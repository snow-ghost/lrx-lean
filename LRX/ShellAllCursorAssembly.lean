import LRX.ShellCursorGapCases
import LRX.EnclosingCoincidentCursorWord

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem shell_all_cursor_word (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (Q C : State n)
    (hCs : C.support=insert (⟨n-1,by omega⟩ : Fin n)
      (insert (⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩ : Fin n)
        (prefixSourceCore p)))
    (hbelow : FiniteRankOrder.Below p.symm
      (Q*Equiv.swap (componentRight p 0) ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩))
    (hC : C ∈ (Q*Equiv.swap (componentRight p 0)
      ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩).cycleFactorsFinset)
    (start finish : Fin n) (K : ℤ) (hK : 0 ≤ K)
    (hinner : InternalShellGapWords p Q C hm start finish)
    (hexterior : ExteriorShellGapWords p Q C hm start finish)
    (htwo : start ≠ finish → EnclosingPositiveArcs C start finish →
      ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
        (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
          (∑ i, |displacement (Q*Equiv.swap (componentRight p 0)
            ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩) i|)+K) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
        (∑ i, |displacement (Q*Equiv.swap (componentRight p 0)
          ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩) i|)+K := by
  classical
  obtain ⟨hzero,hright,hwidth⟩ := prefix_component_source_ends p hc
    (component_card_lt_of_multiple_roots p hm 0)
  have h0 : (0 : Fin n) ∈ C.support := by
    rw [hCs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hzero,by change 0 < (componentSet p 0).card; omega⟩))
  have hz : (⟨n-1,by omega⟩ : Fin n) ∈ C.support := by rw [hCs]; simp
  rcases enclosing_cursor_cases hn C (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hC).1 h0 hz start finish
    with htwoCase | hgap | hlast
  · exact htwo htwoCase.1 htwoCase.2
  · rcases shell_cursor_gap_cases p hm hc C hCs start finish hgap with hi | he | hb
    · obtain ⟨B,hB,hlo,hhi⟩ := hi
      obtain ⟨a,b,hao,hbe,hword⟩ := hinner B hB
      obtain ⟨w,hw,hl⟩ := hword (by omega) (by omega)
      exact ⟨w,hw,by linarith⟩
    · obtain ⟨w,hw,hl⟩ := hexterior he.1 he.2
      exact ⟨w,hw,by linarith⟩
    · have hrC : componentRight p 0 ∈ C.support := by
        rw [hCs]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hright,by omega⟩))
      obtain ⟨w,hw,hl⟩ := enclosing_root_cursor_word hn p _ C hbelow hC h0 hz _ hrC
      have hload := port_load_nonneg (displacement C) (componentRight p 0)
      refine ⟨w,?_,by linarith⟩
      simpa only [hb.1,hb.2] using hw
  · obtain ⟨w,hw,hl⟩ := enclosing_last_cursor_word hn p _ C hbelow hC h0 hz start finish hlast.1 hlast.2
    exact ⟨w,hw,by linarith⟩

#print axioms shell_all_cursor_word
end LRX.FiniteCuts

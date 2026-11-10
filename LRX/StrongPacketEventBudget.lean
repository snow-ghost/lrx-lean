module

public import LRX.SpanningEventForest
public import LRX.PeakActivityBound

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords ZeroGap FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The actual load-component and filling-cycle roots now give a strong cover. -/
theorem source_packet_strong_event_cover (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (events : List (Event n))
    (hprod : (events.map eventSwap).prod=p) (hsep : events.Pairwise LaterOutside)
    (htravel : ∀ i, Travel events i (p.symm i) (displacement p.symm i)) :
    p.support.card+p.cycleFactorsFinset.card ≤
      events.length+2*(componentRoots p).card+2*(fillingCycles p).card := by
  classical
  let roots := p.supportᶜ.toList ++ (componentRoots p).toList ++
    (fillingCycles p).toList.map cycleRoot
  have hcover (i : Fin n) : ∃ r ∈ roots, EventReaches events r i := by
    by_cases hi : i ∈ p.support
    · by_cases hs : i ∈ sourcePackets p
      · obtain ⟨a,ha,hpath⟩ := component_roots_cover p i ((mem_support_inverse p i).mp hi)
        have hp := component_root_reaches hn p hm a ha i ((mem_support_inverse p i).mp hi) hpath
        have hc : PrunedLift.InCore p (displacement p.symm) a i :=
          ⟨hp,((mem_source_packets p i).mp hs).2 a hp⟩
        refine ⟨a,?_,core_event_reachable hprod hsep htravel hc⟩
        simp only [roots,List.mem_append,List.mem_map,Finset.mem_toList]
        exact Or.inl (Or.inr ha)
      · have hinv : i ∈ (p⁻¹).support := by simpa only [Equiv.Perm.support_inv] using hi
        obtain ⟨q,hq,hiq⟩ := (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).mp hinv
        have hqfill : q ∈ fillingCycles p := by
          apply Finset.mem_filter.mpr
          refine ⟨hq,Finset.disjoint_left.mpr ?_⟩
          intro j hj hjs
          have hc := (cycle_root_same_cycle hq hiq).symm.trans (cycle_root_same_cycle hq hj)
          exact hs (source_packets_predecessor_closed p i j (Or.inl hc) hjs)
        refine ⟨cycleRoot q,?_,cycle_event_reachable events p hprod (cycle_root_same_cycle hq hiq)⟩
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨q,Finset.mem_toList.mpr hqfill,rfl⟩
    · refine ⟨i,?_,Relation.ReflTransGen.refl⟩
      apply List.mem_append_left
      apply List.mem_append_left
      exact Finset.mem_toList.mpr (Finset.mem_compl.mpr hi)
  have h := strong_root_cover_count events p hprod roots hcover
  simp only [roots,List.length_append,List.length_map,Finset.length_toList,
    Finset.card_compl,Finset.card_univ,Fintype.card_fin] at h
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  omega

/-- Strong aggregate bound using actual source packets and filling peaks.
No defect decomposition over packets or load components is a premise. -/
theorem aggregate_source_filling_strong_defect (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) :
    let Z := (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
      (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ)
    Z-2*((componentRoots p).card : ℤ) ≤
      2*((∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
        (p.support.card : ℤ)+fillingHalfPeakSum p) := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  obtain ⟨events,hprod,hlen,_,_,hsep,_,htravel⟩ := sorting_events hd (majorized_short hd hmaj)
  have hc := source_packet_strong_event_cover hn p hm events hprod hsep htravel
  have hc' : (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ) ≤
      (events.length : ℤ)+2*((componentRoots p).card : ℤ)+2*((fillingCycles p).card : ℤ) := by
    exact_mod_cast hc
  have hF : (fun i : Fin n => (i : ℤ)+displacement p.symm i)=
      (fun i : Fin n => (p.symm i : ℤ)) := by funext i; simp [displacement]
  rw [hF,canonical_inversion_count] at hlen
  have hI : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  rw [hI] at hlen
  have hS := filling_half_peak_sum_ge_count p
  dsimp only
  linarith

#print axioms source_packet_strong_event_cover
#print axioms aggregate_source_filling_strong_defect
end LRX.FiniteCuts

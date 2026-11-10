import LRX.EnclosingSelectedArcWord
import LRX.PeakServiceArcPartition
import LRX.GlobalPeakServiceFamily
import LRX.TwoArcServiceWord
import LRX.CyclePartSelection

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem cycle_peak_arc_ports (C : State n) (hC : C.IsCycle)
    (start finish : Fin n) (hne : start ≠ finish)
    (hboth : ∀ dir : Bool, ∃ r ∈ C.support, ∃ port : Fin n,
      (port=r ∨ port+1=r) ∧
      (arcCoordinate dir start port).val ≤ (arcCoordinate dir start finish).val ∧
      0 < portLoad (displacement C) port) :
    ∃ roots ports : Bool → Fin n,
      (∀ dir, roots dir ∈ C.support) ∧
      (∀ dir, ports dir=roots dir ∨ ports dir+1=roots dir) ∧
      (∀ dir, (arcCoordinate dir start (ports dir)).val ≤ (arcCoordinate dir start finish).val) ∧
      2*(leftPeak C n : ℤ)+2 ≤
        portLoad (displacement C) (ports true)+portLoad (displacement C) (ports false) := by
  classical
  choose roots hroots ports hinc hrange hpos using hboth
  obtain ⟨good,hgood,_,hpeak⟩ := left_peak_port C n le_rfl (cycle_global_peak_positive C hC)
  have hgoodmem : good ∈ C.support := Equiv.Perm.mem_support.mpr hgood
  have hpeak' : portLoad (displacement C) good=2*(leftPeak C n : ℤ) := by
    rw [port_load_eq_twice_half,hpeak]
  have hbase (dir : Bool) : 2 ≤ portLoad (displacement C) (ports dir) := by
    have hh := hpos dir
    rw [port_load_eq_twice_half] at hh ⊢
    omega
  by_cases hg : (arcCoordinate true start good).val ≤ (arcCoordinate true start finish).val
  · refine ⟨(fun dir => if dir then good else roots false),
      (fun dir => if dir then good else ports false),?_,?_,?_,?_⟩
    · intro dir; cases dir
      · exact hroots false
      · exact hgoodmem
    · intro dir; cases dir
      · exact hinc false
      · exact Or.inl rfl
    · intro dir; cases dir
      · exact hrange false
      · exact hg
    · have hb := hbase false
      simp only [ite_true,Bool.false_eq_true,ite_false]
      omega
  · have hg' := arc_not_forward_is_reverse start finish good hne hg
    refine ⟨(fun dir => if dir then roots true else good),
      (fun dir => if dir then ports true else good),?_,?_,?_,?_⟩
    · intro dir; cases dir
      · exact hgoodmem
      · exact hroots true
    · intro dir; cases dir
      · exact Or.inl rfl
      · exact hinc true
    · intro dir; cases dir
      · exact hg'
      · exact hrange true
    · have hb := hbase true
      simp only [ite_true,Bool.false_eq_true,ite_false]
      omega

/-- All non-root cycles are automatically split between the two arcs.
The only geometric input is a pair of incident root ports with the stated
aggregate load; no service family or rank-transfer certificate is supplied. -/
theorem enclosing_two_arc_word (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p G.symm)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (start finish : Fin n) (hne : start ≠ finish)
    (roots ports : Bool → Fin n)
    (hroots : ∀ dir, roots dir ∈ C.support)
    (hincident : ∀ dir, ports dir=roots dir ∨ ports dir+1=roots dir)
    (hrange : ∀ dir, (arcCoordinate dir start (ports dir)).val ≤
      (arcCoordinate dir start finish).val)
    (hload : 2*(leftPeak C n : ℤ)+2 ≤
      portLoad (displacement C) (ports true)+portLoad (displacement C) (ports false)) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)+
        (n/2 : ℕ)-(leftPeak C n : ℤ)-
        (∑ D ∈ G.cycleFactorsFinset.erase C, (leftPeak D n : ℤ))-1 := by
  classical
  let all := (G.cycleFactorsFinset.erase C).toList
  have hmem (D : State n) (hD : D ∈ all) : D ≠ C ∧ D ∈ G.cycleFactorsFinset :=
    Finset.mem_erase.mp (Finset.mem_toList.mp hD)
  have hcy (D : State n) (hD : D ∈ all) : D.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hmem D hD).2).1
  have hdis : all.Pairwise Equiv.Perm.Disjoint := by
    apply (Finset.nodup_toList _).imp_of_mem
    intro D E hD hE hne
    exact G.cycleFactorsFinset_pairwise_disjoint (hmem D hD).2 (hmem E hE).2 hne
  obtain ⟨ss,hst,hcan,hprice⟩ := global_peak_service_family hn all hcy
  have hsdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target) := by
    apply List.pairwise_map.mp
    rw [hst]
    exact inverse_targets_disjoint all hdis
  have hfactor (a : ExactService n) (ha : a ∈ ss) :
      a.service.target⁻¹ ≠ C ∧ a.service.target⁻¹ ∈ G.cycleFactorsFinset := by
    have hh : a.service.target ∈ ss.map (fun s => s.service.target) := List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [hst] at hh
    obtain ⟨D,hD,hDa⟩ := List.mem_map.mp hh
    rw [← hDa,inv_inv]
    exact hmem D hD
  let saving : ExactService n → ℤ := fun a => 2*(leftPeak a.service.target⁻¹ n : ℤ)
  let selected := peakArcServices start finish ss
  have hw (dir : Bool) : ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)-
        portLoad (displacement C) (ports dir)-((selected dir).map saving).sum+
        ((arcCoordinate dir start finish).val : ℤ) := by
    have hsmem (a : ExactService n) (ha : a ∈ selected dir) : a ∈ ss :=
      peak_arc_services_mem start finish ss dir ha
    have hsd := peak_arc_services_disjoint start finish ss hsdis dir
    apply enclosing_selected_arc_word hn p G C hbelow hC hzero hlast (selected dir)
      hsd (peak_arc_services_canonical start finish ss hcan dir)
    · apply CyclePart.product _ G.symm (List.pairwise_map.mpr hsd)
      intro t ht
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
      simpa only [inv_inv,Equiv.Perm.inv_def,Equiv.symm_symm] using
        CyclePart.inverse (CyclePart.cycle_factor (hfactor a (hsmem a ha)).2)
    · apply Equiv.Perm.disjoint_prod_right
      intro t ht
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
      obtain ⟨hneq,hfac⟩ := hfactor a (hsmem a ha)
      simpa only [inv_inv] using
        (G.cycleFactorsFinset_pairwise_disjoint hC hfac (Ne.symm hneq)).inv_right
    · exact fun a ha => le_of_eq (hprice a (hsmem a ha))
    · exact hroots dir
    · exact hincident dir
    · exact hrange dir
    · exact peak_arc_services_range start finish hne ss dir
  have hsaving := peak_arc_services_savings start finish ss saving
  have hsum : (ss.map saving).sum=2*(∑ D ∈ G.cycleFactorsFinset.erase C, (leftPeak D n : ℤ)) := by
    have he := congrArg (List.map (fun q : State n => 2*(leftPeak q⁻¹ n : ℤ))) hst
    have he' : ss.map saving=all.map (fun q => 2*(leftPeak q n : ℤ)) := by
      simpa only [saving,List.map_map,Function.comp_def,inv_inv] using he
    rw [he',← List.sum_toFinset _ (Finset.nodup_toList _)]
    simp only [all,Finset.toList_toFinset,Finset.mul_sum]
  rw [hsum] at hsaving
  obtain ⟨wl,hwl,hll⟩ := hw true
  obtain ⟨wr,hwr,hlr⟩ := hw false
  have harcs : ((arcCoordinate true start finish).val : ℤ)+
      ((arcCoordinate false start finish).val : ℤ)=(n : ℤ) := by
    exact_mod_cast complementary_arc_lengths start finish hne
  have hn' : (n : ℤ) ≤ 2*((n/2 : ℕ) : ℤ)+1 := by omega
  by_cases hl : (wl.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)+
      (n/2 : ℕ)-(leftPeak C n : ℤ)-
      (∑ D ∈ G.cycleFactorsFinset.erase C, (leftPeak D n : ℤ))-1
  · exact ⟨wl,hwl,hl⟩
  · exact ⟨wr,hwr,by dsimp only [selected] at hll hlr; omega⟩

#print axioms enclosing_two_arc_word

/-- A lower-map word in the genuine two-positive-root-arcs case; all root
ports, selected children and service words are constructed internally. -/
theorem enclosing_positive_arcs_word (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p.symm G)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (start finish : Fin n) (hne : start ≠ finish)
    (hboth : ∀ dir : Bool, ∃ r ∈ C.support, ∃ port : Fin n,
      (port=r ∨ port+1=r) ∧
      (arcCoordinate dir start port).val ≤ (arcCoordinate dir start finish).val ∧
      0 < portLoad (displacement C) port) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)+
        (n/2 : ℕ)-(leftPeak C n : ℤ)-
        (∑ D ∈ G.cycleFactorsFinset.erase C, (leftPeak D n : ℤ))-1 := by
  obtain ⟨roots,ports,hr,hi,hra,hl⟩ := cycle_peak_arc_ports C
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hC).1 start finish hne hboth
  have hlow : FiniteRankOrder.Below p G.symm := by
    simpa only [Equiv.symm_symm,Equiv.Perm.inv_def] using
      (FiniteRankOrder.below_inverse_iff p.symm G).mpr hbelow
  exact enclosing_two_arc_word hn p G C hlow hC hzero hlast start finish hne roots ports hr hi hra hl

#print axioms cycle_peak_arc_ports
#print axioms enclosing_positive_arcs_word
end LRX.FiniteCuts

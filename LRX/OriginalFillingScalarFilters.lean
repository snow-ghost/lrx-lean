module

public import LRX.OriginalFillingFixedBudget
public import LRX.PrefixFillingSize

@[expose] public section

/-! M4 filters expressed with actual x=L-R0 and f-a, not independent
width or fixed-position certificates. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

/-- Scalar-search internal-window filters, all derived from the original
unpaid maximal-cut map and the same chosen large component. -/
theorem original_unpaid_filling_scalar_filters (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let As := positiveSourceFamily q L
    let x := L-(prefixSourceCore q).card
    let a := (singletonSuffixComponents q L).card
    let f := n-p.support.card
    let T := scalarFillingBudget p root
    (As.map (fun A => A.size)).sum=x ∧ 0 ≤ T ∧
    (x : ℤ) ≤ 2*T+(f : ℤ)-(a : ℤ) ∧
    (As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤
      2*T*(T+if a<f then 1 else 0) ∧
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤ 4*T^2+2*T+(x : ℤ) := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let As := positiveSourceFamily q L
  let x := L-(prefixSourceCore q).card
  let a := (singletonSuffixComponents q L).card
  let f := n-p.support.card
  let T := scalarFillingBudget p root
  have hp := component_cut_internal_size_partition p (by omega) root (by omega)
  change (As.map (fun A => A.size)).sum+(prefixSourceCore q).card=L at hp
  have hsNat : (As.map (fun A => A.size)).sum=x := by dsimp only [x]; omega
  have hsInt : (As.map (fun A => (A.size : ℤ))).sum=(x : ℤ) := by
    have hh := congrArg (fun z : ℕ => (z : ℤ)) hsNat
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hh
  have hT := (original_unpaid_scalar_filling_filters hn p hmaj hmax hc hk root hlarge hpos).1
  have hw := original_unpaid_prefix_width_fixed_filter hn p hmaj hmax hc hk root hlarge hpos
  change (As.map (fun A => (A.size : ℤ))).sum ≤ 2*T+(f : ℤ)-(a : ℤ)-
    2*(As.map (fun A => cycleDefect A.filling)).sum at hw
  rw [hsInt] at hw
  have hZ : 0 ≤ (As.map (fun A => cycleDefect A.filling)).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨A,_,rfl⟩ := List.mem_map.mp hz
    have hd := finite_depth_rank A.filling
    unfold cycleDefect
    omega
  have he := original_unpaid_prefix_energy_indicator hn p hmaj hmax hc hk root hlarge hpos
  have hq := (original_unpaid_prefix_filling_filters hn p hmaj hmax hc hk root hlarge hpos).2.2
  change (As.map (fun A => (A.size : ℤ)^2)).sum ≤ 4*T^2+2*T+
    (As.map (fun A => (A.size : ℤ))).sum at hq
  rw [hsInt] at hq
  have hwidth : (x : ℤ) ≤ 2*T+(f : ℤ)-(a : ℤ) := by omega
  exact ⟨hsNat,hT,hwidth,he,hq⟩

#print axioms original_unpaid_filling_scalar_filters
end LRX.FiniteCuts

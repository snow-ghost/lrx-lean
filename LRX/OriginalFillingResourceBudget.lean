import LRX.WindowCyclePeakFamily
import LRX.FillingPeakRecenter
import LRX.LargeComponentNumericReserve
import LRX.PeakReserveBound

/-! M4: the real kappa budget follows from original unpaid peak data and C7.
The normalized windows and the original route are linked by filling-peak invariance. -/
namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ}

theorem filling_resource_sum_eq (As : List (FillingWindow n)) :
    (As.map FillingWindow.resource).sum=(As.map FillingWindow.deficit).sum+
      (As.map (fun A => (cyclePeakSum A.filling : ℤ))).sum := by
  induction As with
  | nil => simp
  | cons A As ih =>
    simp only [List.map_cons,List.sum_cons,ih,FillingWindow.resource,
      fillingResource,FillingWindow.deficit]
    ring
end LRX.FiniteWindow

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

/-- The actual internal filling resource is bounded at the chosen component cut.
No scalar budget, peak-sum comparison or cut-invariance certificate is supplied. -/
theorem original_unpaid_filling_resource_budget (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
    let a := (singletonSuffixComponents q L).card
    let M : ℤ := 2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))+(a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ)
    let eps : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    ((positiveSourceFamily q n).map FillingWindow.resource).sum ≤
      2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
        (sourceHalfPeak p : ℤ)-3-M-eps := by
  have hC7 := large_component_numeric_reserve hn p hmaj (by omega) root hlarge
  have hpeaks := positive_filling_peak_sum_le (localTarget p 0 (componentLeft p root)) n
  rw [component_cut_filling_half_peak_sum] at hpeaks
  have hresource := filling_resource_sum_eq (positiveSourceFamily (localTarget p 0 (componentLeft p root)) n)
  have hchoose := choose_two_half_identity n
  unfold peakExcess at hpos
  dsimp only at hC7 ⊢
  linarith

/-- Scalar T used by the finite search, with normalized actual a,t,v and
maximal-cut bridge upper bound a+t-1[a>0]. -/
noncomputable def scalarFillingBudget (p : State n) (root : Fin n) : ℤ :=
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let t := (nontrivialSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  let a := (singletonSuffixComponents q L).card
  let B : ℤ := if a=0 then (t : ℤ) else (a : ℤ)+(t : ℤ)-1
  let M : ℤ := 2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))+(a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ)
  let eps : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  2*B+((n/2 : ℕ) : ℤ)-(sourceHalfPeak p : ℤ)-3-M-eps

/-- The finite-search scalar budget is an actual consequence of the unpaid
maximal-cut map; it is not a supplied certificate. -/
theorem original_unpaid_scalar_filling_budget (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    ((positiveSourceFamily (localTarget p 0 (componentLeft p root)) n).map FillingWindow.resource).sum ≤
      scalarFillingBudget p root := by
  have hb := original_unpaid_filling_resource_budget hn p hmaj hc hk root hlarge hpos
  have hbridge := maximal_bridge_bounds_at_component_cut hn p hmax hc hk root (by omega)
  have hcount := component_cut_external_count p root (by omega)
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let t := (nontrivialSuffixComponents q L).card
  let a := (singletonSuffixComponents q L).card
  have ht : t=k := by change t+1=(componentRoots p).card at hcount; omega
  change ((a : ℤ)=0 → (bridgeBudget (componentBridges p hc) : ℤ) ≤ (k : ℤ)) ∧
    (1 ≤ (a : ℤ) → (bridgeBudget (componentBridges p hc) : ℤ) ≤ (a : ℤ)+(k : ℤ)-1) at hbridge
  have hcap : (bridgeBudget (componentBridges p hc) : ℤ) ≤
      if a=0 then (t : ℤ) else (a : ℤ)+(t : ℤ)-1 := by
    split_ifs with ha
    · have hh := hbridge.1 (by omega)
      omega
    · have hh := hbridge.2 (by omega)
      omega
  dsimp only [q,L,t,a] at hcap
  dsimp only [scalarFillingBudget] at ⊢
  dsimp only at hb
  linarith

/-- The normalized real window filters with the exact scalar-search T. -/
theorem original_unpaid_scalar_filling_filters (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    let As := positiveSourceFamily (localTarget p 0 (componentLeft p root)) n
    let T := scalarFillingBudget p root
    0 ≤ T ∧
    (As.map (fun A => (A.size : ℤ))).sum ≤ 2*T+
      (As.map (fun A => ((A.size-A.filling.support.card : ℕ) : ℤ))).sum-
      2*(As.map (fun A => cycleDefect A.filling)).sum ∧
    (As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤ 2*T*(T+1) ∧
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤ 4*T^2+2*T+
      (As.map (fun A => (A.size : ℤ))).sum := by
  have hb := original_unpaid_scalar_filling_budget hn p hmaj hmax hc hk root hlarge hpos
  exact ⟨(filling_resource_sum_nonneg _).trans hb,filling_family_resource_budget _ _ hb⟩

#print axioms original_unpaid_filling_resource_budget
#print axioms original_unpaid_scalar_filling_budget
#print axioms original_unpaid_scalar_filling_filters
end LRX.FiniteCuts

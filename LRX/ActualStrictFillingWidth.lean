module

public import LRX.StrictFillingFamilyWidth
public import LRX.ActualNonshortFillings

@[expose] public section

namespace LRX.FiniteCuts
open RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem actual_zero_width_four_stronger_width_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hx : 0 < (componentSet p root).card-
      (prefixSourceCore (localTarget p 0 (componentLeft p root))).card) :
    (((componentSet p root).card-
      (prefixSourceCore (localTarget p 0 (componentLeft p root))).card : ℕ) : ℤ) ≤
      2*scalarFillingBudget p root-5 := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let As := positiveSourceFamily q L
  let x := L-(prefixSourceCore q).card
  have hZ := actual_zero_width_four_positive_filling_defect_sum hn p hmaj hmax hc hk
    root hlarge ht hpos he hp hv hx
  change 2 ≤ (As.map (fun A => cycleDefect A.filling)).sum at hZ
  have hfull := zero_energy_even_full_support p hmaj he hp
  have hfixed := component_cut_filling_fixed_partition p (by omega) root (by omega)
  have hfa : n-p.support.card=(singletonSuffixComponents q L).card := by
    change _+_+(singletonSuffixComponents q L).card=n-p.support.card at hfixed
    omega
  have hf : ∀ A ∈ As, A.filling.support.card=A.size :=
    fun A hA => component_cut_prefix_fixed_free p (by omega) root (by omega) hfa A hA
  have hspec := positive_source_family_spec q L
  have hmin := actual_zero_width_four_large_min_arrow hn p hmaj hmax hc hk root hlarge ht hpos he hp hv
  have hlocal : ∀ A ∈ As, ∀ i, 3 ≤ |displacement A.filling i| := by
    intro A hA i
    have hm := hspec.1 A hA
    have hb := hspec.2.2.1 A hA
    rw [← matching_window_displacement A.window q.symm A.filling hm i]
    apply hmin
    have hi := contains_embed A.window i
    have hh := hi.2
    change (embed A.window i).val < L
    omega
  have hbudget := original_unpaid_prefix_filling_budget hn p hmaj hmax hc hk root hlarge hpos
  have hwidth := (original_unpaid_filling_scalar_filters hn p hmaj hmax hc hk root hlarge hpos).1
  change (As.map (fun A => A.size)).sum=x at hwidth
  have hcast : (As.map (fun A => (A.size : ℤ))).sum=(x : ℤ) := by
    have hh := congrArg (fun z : ℕ => (z : ℤ)) hwidth
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hh
  have hw := nonshort_family_strict_width As (scalarFillingBudget p root) hf hlocal hbudget
    (by rw [hcast]; change 0 < (x : ℤ); exact_mod_cast hx) hZ
  rw [hcast] at hw
  exact hw

#print axioms actual_zero_width_four_stronger_width_reserve
end LRX.FiniteCuts

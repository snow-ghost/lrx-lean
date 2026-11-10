module

public import LRX.WindowFamilyFixedCount
public import LRX.PrefixFillingResourceBudget

@[expose] public section

/-! M4: replace local fixed counts by the actual scalar f-a and obtain the
energy filter with indicator 1[f>a], including f=a>0. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

theorem component_cut_filling_fixed_partition (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hsize : 2 ≤ (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    ((positiveSourceFamily q L).map (fun A => A.size-A.filling.support.card)).sum+
      ((suffixComponentFamily q L).map (fun A => A.size-A.filling.support.card)).sum+
      (singletonSuffixComponents q L).card=n-p.support.card := by
  let q := localTarget p 0 (componentLeft p root)
  have hzero : (componentSet q 0).card=(componentSet p root).card := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have he : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← he] at hh
  have hproper := component_card_lt_of_multiple_roots p hm root
  have hs : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have hh := prefix_external_filling_fixed_partition q (by omega) (by omega)
  rw [hzero,hs] at hh
  exact hh

theorem component_cut_prefix_fixed_free (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hsize : 2 ≤ (componentSet p root).card)
    (hfa : n-p.support.card=(singletonSuffixComponents
      (localTarget p 0 (componentLeft p root)) (componentSet p root).card).card)
    (A : FillingWindow n)
    (hA : A ∈ positiveSourceFamily (localTarget p 0 (componentLeft p root)) (componentSet p root).card) :
    A.filling.support.card=A.size := by
  have hh := component_cut_filling_fixed_partition p hm root hsize
  dsimp only at hh
  have hterm : A.size-A.filling.support.card ≤
      ((positiveSourceFamily (localTarget p 0 (componentLeft p root)) (componentSet p root).card).map
        (fun A => A.size-A.filling.support.card)).sum := by
    apply List.single_le_sum
    · intro x _; exact Nat.zero_le x
    · exact List.mem_map.mpr ⟨A,hA,rfl⟩
  have hcard : A.filling.support.card ≤ A.size := by simpa using Finset.card_le_univ A.filling.support
  omega

/-- The real width filter with scalar f-a, not a supplied sum of fixed points. -/
theorem original_unpaid_prefix_width_fixed_filter (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let As := positiveSourceFamily q L
    let a := (singletonSuffixComponents q L).card
    (As.map (fun A => (A.size : ℤ))).sum ≤ 2*scalarFillingBudget p root+
      ((n-p.support.card : ℕ) : ℤ)-(a : ℤ)-2*(As.map (fun A => cycleDefect A.filling)).sum := by
  let As := positiveSourceFamily (localTarget p 0 (componentLeft p root)) (componentSet p root).card
  let a := (singletonSuffixComponents (localTarget p 0 (componentLeft p root)) (componentSet p root).card).card
  have hh := component_cut_filling_fixed_partition p (by omega) root (by omega)
  have hle : (As.map (fun A => A.size-A.filling.support.card)).sum+a ≤ n-p.support.card := by
    change (As.map (fun A => A.size-A.filling.support.card)).sum+
      ((suffixComponentFamily (localTarget p 0 (componentLeft p root)) (componentSet p root).card).map
        (fun A => A.size-A.filling.support.card)).sum+a=n-p.support.card at hh
    omega
  have hcast : (((As.map (fun A => A.size-A.filling.support.card)).sum : ℕ) : ℤ)+(a : ℤ) ≤
      ((n-p.support.card : ℕ) : ℤ) := by exact_mod_cast hle
  have heq : (((As.map (fun A => A.size-A.filling.support.card)).sum : ℕ) : ℤ)=
      (As.map (fun A => ((A.size-A.filling.support.card : ℕ) : ℤ))).sum := by simp [Function.comp_def]
  rw [heq] at hcast
  have hw := (original_unpaid_prefix_filling_filters hn p hmaj hmax hc hk root hlarge hpos).1
  change (As.map (fun A => (A.size : ℤ))).sum ≤ 2*scalarFillingBudget p root+
    (As.map (fun A => ((A.size-A.filling.support.card : ℕ) : ℤ))).sum-
    2*(As.map (fun A => cycleDefect A.filling)).sum at hw
  change (As.map (fun A => (A.size : ℤ))).sum ≤ 2*scalarFillingBudget p root+
    ((n-p.support.card : ℕ) : ℤ)-(a : ℤ)-2*(As.map (fun A => cycleDefect A.filling)).sum
  omega

/-- The f=a case, including nonzero isolated fixed positions. -/
theorem original_unpaid_equal_fixed_prefix_filter (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc)
    (hfa : n-p.support.card=(singletonSuffixComponents
      (localTarget p 0 (componentLeft p root)) (componentSet p root).card).card) :
    let As := positiveSourceFamily (localTarget p 0 (componentLeft p root)) (componentSet p root).card
    let T := scalarFillingBudget p root
    (As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤
      2*(T-(As.map (fun A => cycleDefect A.filling)).sum)^2 ∧
    2*(T-(As.map (fun A => cycleDefect A.filling)).sum)^2 ≤ 2*T^2 := by
  exact fixed_free_filling_family_budget _ _
    (fun A hA => component_cut_prefix_fixed_free p (by omega) root (by omega) hfa A hA)
    (original_unpaid_prefix_filling_budget hn p hmaj hmax hc hk root hlarge hpos)

/-- Exact energy filter used by the scalar search: 2T(T+1[f>a]). -/
theorem original_unpaid_prefix_energy_indicator (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let a := (singletonSuffixComponents q L).card
    let T := scalarFillingBudget p root
    ((positiveSourceFamily q L).map (fun A => ∑ i, |displacement A.filling i|)).sum ≤
      2*T*(T+if a<n-p.support.card then 1 else 0) := by
  dsimp only
  by_cases h : (singletonSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card<n-p.support.card
  · simpa only [ite_eq_left h] using
      (original_unpaid_prefix_filling_filters hn p hmaj hmax hc hk root hlarge hpos).2.1
  · have hh := component_cut_filling_fixed_partition p (by omega) root (by omega)
    dsimp only at hh
    have hfa : n-p.support.card=(singletonSuffixComponents
      (localTarget p 0 (componentLeft p root)) (componentSet p root).card).card := by omega
    have he := original_unpaid_equal_fixed_prefix_filter hn p hmaj hmax hc hk root hlarge hpos hfa
    simpa only [ite_eq_right h,add_zero,pow_two,mul_assoc] using he.1.trans he.2

#print axioms component_cut_filling_fixed_partition
#print axioms original_unpaid_prefix_width_fixed_filter
#print axioms original_unpaid_equal_fixed_prefix_filter
#print axioms original_unpaid_prefix_energy_indicator
end LRX.FiniteCuts

import LRX.InnermostEventComponent
import LRX.StrongPacketEventBudget
import LRX.LinearSortingTrace
import LRX.ActualGlobalNonshortDefect

/-! M4, even zero-energy exterior width four, U=4.
Equality in the actual budget reduces the event slack from two to one. -/
namespace LRX.FiniteCuts
open ZeroGap RotationWords FiniteWindow
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem peak_four_source_rigidity (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc)
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (hv : (∑ C ∈ nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card, C.card : ℕ)=4)
    (hU : sourceHalfPeak p=4) :
    (componentRoots p).card=3 ∧ bridgeBudget (componentBridges p hc)=2 ∧
      peakExcess p hc=1 ∧ cycleDefect p=2 ∧
      (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
        (p.support.card : ℤ)+fillingHalfPeakSum p = -2 ∧
      fillingHalfPeakSum p=((fillingCycles p).card : ℤ) ∧
      p.cycleFactorsFinset.card=(fillingCycles p).card+4 := by
  classical
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hsize : 2 ≤ (componentSet p root).card := by omega
  have hf := zero_energy_even_full_support p hmaj he hp
  have hfixed := component_cut_filling_fixed_partition p (by omega) root hsize
  have ha : (singletonSuffixComponents q L).card=0 := by
    change _+_+(singletonSuffixComponents q L).card=n-p.support.card at hfixed
    omega
  have hw := nontrivial_suffix_size_sum q L
  have hcount := component_cut_external_count p root hsize
  change 2*(nontrivialSuffixComponents q L).card ≤
    (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ) at hw
  change (∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ)=4 at hv
  change 2 ≤ (nontrivialSuffixComponents q L).card at ht
  change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
  have hroots : (componentRoots p).card=3 := by omega
  have hk2 : k=2 := by omega
  have hB := (maximal_bridge_bounds_at_component_cut hn p hmax hc hk root hsize).1
    (by change ((singletonSuffixComponents q L).card : ℤ)=0; rw [ha]; rfl)
  have hz := (actual_zero_width_four_peak_le_four hn p hmaj hmax hc hk root
    hlarge ht hpos he hp hv).2 hU
  let C := (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+fillingHalfPeakSum p
  have hN := choose_two_half_identity n
  have hsizeN : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by omega
  have hprice : peakExcess p hc=2*(bridgeBudget (componentBridges p hc) : ℤ)-
      (sourceHalfPeak p : ℤ)-1-C := by
    unfold peakExcess
    dsimp only [C]
    unfold canonicalEnergyDeficit at he
    rw [hf]
    nlinarith only [he,hN,hsizeN]
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  obtain ⟨events,hprod,hlen,_,_,hsep,_,htravel⟩ := sorting_events hd (majorized_short hd hmaj)
  have hstrong := source_packet_strong_event_cover hn p (by omega) events hprod hsep htravel
  have hF : (fun i : Fin n => (i : ℤ)+displacement p.symm i)=
      (fun i => (p.symm i : ℤ)) := by funext i; simp [displacement]
  have hI : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  rw [hF,canonical_inversion_count,hI] at hlen
  have hS := filling_half_peak_sum_ge_count p
  have hZ : C=cycleDefect p-(p.cycleFactorsFinset.card : ℤ)+fillingHalfPeakSum p := by
    simp only [C,cycleDefect,displacement_mass_inverse]
    ring
  change _ ∧ _ ∧ _ ∧ _ ∧ C= -2 ∧ _ ∧ _
  omega

/-- Every actual filling cycle has half-peak one once the sum equals its
cycle count; this is the precise extra premise used by manuscript D3. -/
theorem filling_cycles_peak_one_of_equality (p : State n)
    (heq : fillingHalfPeakSum p=((fillingCycles p).card : ℤ)) :
    ∀ q ∈ fillingCycles p, leftPeak q n=1 := by
  classical
  have hpos (q : State n) (hq : q ∈ fillingCycles p) : 1 ≤ leftPeak q n := by
    have hcy := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (Finset.mem_filter.mp hq).1).1
    obtain ⟨i,hi⟩ := hcy.nonempty_support
    exact moved_global_peak_positive q i (Equiv.Perm.mem_support.mp hi)
  have hsum : (∑ q ∈ fillingCycles p, (leftPeak q n : ℤ))=((fillingCycles p).card : ℤ) := by
    rw [← heq]
    unfold fillingHalfPeakSum
    simpa only [Finset.toList_toFinset] using
      List.sum_toFinset (fun q : State n => (leftPeak q n : ℤ)) (Finset.nodup_toList (fillingCycles p))
  intro q hq
  have hrest := Finset.sum_le_sum (s := (fillingCycles p).erase q)
    (f := fun _ => (1 : ℤ)) (g := fun q => (leftPeak q n : ℤ))
    (fun r hr => by exact_mod_cast hpos r (Finset.mem_of_mem_erase hr))
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_erase_of_mem hq] at hrest
  have hadd := Finset.sum_erase_add (fillingCycles p) (fun r => (leftPeak r n : ℤ)) hq
  have hcard := Finset.card_pos.mpr ⟨q,hq⟩
  have hqpos := hpos q hq
  omega

#print axioms peak_four_source_rigidity
#print axioms filling_cycles_peak_one_of_equality
end LRX.FiniteCuts

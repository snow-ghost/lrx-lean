import LRX.ComponentPacketPeak
import LRX.ThreeComponentPacketRoute
import LRX.PeakActivityBound
import LRX.MaximalCutManyRouting

/-! M4's terminal scalar rows now supply their own packet geometry.
An unpaid actual peak forces absence of fillings; global U selects a real packet. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

/-- In a full-support three-component map, the actual bridge budget is at
most two. With U>=4 and deficit>=m-2, any filling already pays the peak. -/
theorem unpaid_three_component_no_fillings (p : State n)
    (hc : (componentRoots p).card=2+1) (hsupport : p.support.card=n)
    (hU : 4 ≤ sourceHalfPeak p) (hpos : 1 ≤ peakExcess p hc)
    (hdeficit : ((n/2 : ℕ) : ℤ)-2 ≤ (n.choose 2 : ℤ)-
      (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)-
      ∑ i, |displacement p.symm i|) : fillingCycles p=∅ := by
  have hB := component_bridge_budget p hc
  rw [hsupport,Nat.sub_self,Nat.zero_add] at hB
  have hS := filling_half_peak_sum_ge_count p
  have hI : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  rw [canonical_inversion_count,hI] at hdeficit
  unfold peakExcess at hpos
  apply Finset.card_eq_zero.mp
  omega

/-- Actual unpaid exceptional peaks are paid for any even size at most 20.
No packet, no-filling or per-packet peak certificate is supplied. -/
theorem unpaid_three_component_source_peak_sharp (hn : 2 ≤ n) (hn20 : n ≤ 20)
    (heven : n%2=0) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=2+1) (hsupport : p.support.card=n)
    (hcycles : p.cycleFactorsFinset.card=4) (hz : cycleDefect p=2)
    (hU : 4 ≤ sourceHalfPeak p) (hpos : 1 ≤ peakExcess p hc)
    (s t : Fin n) :
    ∃ w : List Letter, eval w=(rotation s)⁻¹*p*rotation t ∧ w.length ≤ n.choose 2 := by
  have hdeficit := exceptional_packet_cycle_deficit p heven hmaj hsupport hcycles hz
  have hf := unpaid_three_component_no_fillings p hc hsupport hU hpos hdeficit
  obtain ⟨root,hr,hpeak⟩ := exists_component_packet_peak_ge_source hn p (by omega) (by omega)
  exact three_component_peak_four_sharp hn hn20 p hc hf root hr (by omega) hdeficit s t

/-- Complete payment of the two-arc case for the terminal n=16,20 scalar rows.
Only actual scalar data remain; both signs of the original peak excess are covered. -/
theorem exceptional_source_peak_word (hsize : n=16 ∨ n=20) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=2+1) (hsupport : p.support.card=n)
    (hcycles : p.cycleFactorsFinset.card=4) (hz : cycleDefect p=2)
    (hU : 4 ≤ sourceHalfPeak p) (s t : Fin n) (hne : s ≠ t)
    (hboth : JoinedPositiveArcs p hc s t) :
    ∃ w : List Letter, eval w=(rotation s)⁻¹*p*rotation t ∧ w.length ≤ n.choose 2 := by
  by_cases hpay : peakExcess p hc ≤ 0
  · exact joined_peak_word_of_nonpositive_excess (by omega) p hc (by omega) s t hne hboth hpay
  · exact unpaid_three_component_source_peak_sharp (by omega) (by omega) (by omega)
      p hmaj hc hsupport hcycles hz hU (by omega) s t

/-- Terminal exceptional scalar data give sharp routing for every cursor,
using the existing full gap/two-arc reduction in the original coordinates. -/
theorem exceptional_large_component_sharp_word (hsize : n=16 ∨ n=20) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=2+1) (hsupport : p.support.card=n)
    (hcycles : p.cycleFactorsFinset.card=4) (hz : cycleDefect p=2)
    (hU : 4 ≤ sourceHalfPeak p) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (s t : Fin n) :
    ∃ w : List Letter, eval w=(rotation s)⁻¹*p*rotation t ∧ w.length ≤ n.choose 2 := by
  have ht := component_cut_external_count p root (by omega)
  have ht2 : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card := by omega
  rcases original_cut_sharp_or_two_arc (by omega) p hmaj hc (by omega) root hlarge ht2 s t with h | h
  · exact h
  · exact exceptional_source_peak_word hsize p hmaj hc hsupport hcycles hz hU s t h.1 h.2

#print axioms unpaid_three_component_no_fillings
#print axioms unpaid_three_component_source_peak_sharp
#print axioms exceptional_source_peak_word
#print axioms exceptional_large_component_sharp_word
end LRX.FiniteCuts

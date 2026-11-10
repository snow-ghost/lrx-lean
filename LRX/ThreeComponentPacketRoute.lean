module

public import LRX.ComponentPacketPartition
public import LRX.ThreeCanonicalPackets
public import LRX.TwoWindowCycleDefect
public import LRX.SourceGapSharpPayment

@[expose] public section

/-! M4: extract the three services from the actual component decomposition.
Only the exceptional structural classification and numerical data remain. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Three real load components without filling cycles supply disjoint exact
services whose product and displacements are those of the original map. -/
theorem three_component_packets_sharp (hn : 2 ≤ n) (hn20 : n ≤ 20)
    (p : State n) (hc : (componentRoots p).card=3) (hf : fillingCycles p=∅)
    (hsave : 12 ≤ ((componentRoots p).toList.map (fun r =>
      2*(leftPeak (canonicalRootPacket p r).symm n : ℤ))).sum)
    (hdeficit : ((n/2 : ℕ) : ℤ)-2 ≤ (n.choose 2 : ℤ)-
      (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)-
      ∑ i, |displacement p.symm i|)
    (s t : Fin n) :
    ∃ w : List Letter, eval w=(rotation s)⁻¹*p*rotation t ∧ w.length ≤ n.choose 2 := by
  classical
  let roots := (componentRoots p).toList
  have hnd : roots.Nodup := Finset.nodup_toList _
  have hr (r : Fin n) : r ∈ roots ↔ r ∈ componentRoots p := Finset.mem_toList
  apply three_canonical_packets_sharp hn hn20 p roots
    (by simpa only [roots,Finset.length_toList] using hc)
    (component_packet_list_disjoint p roots hnd (fun r h => (hr r).mp h))
    (component_packet_list_product hn p (by omega) roots hnd hr (source_covers_of_no_fillings p hf))
    (fun r h => component_packet_peak_positive p r ((hr r).mp h)) hsave hdeficit s t

/-- With three real components, one packet peak of four pays twelve rotations:
eight at that packet and at least two at each of the other two. -/
theorem three_component_peak_four_savings (p : State n)
    (hc : (componentRoots p).card=3) (root : Fin n)
    (hr : root ∈ componentRoots p)
    (hbig : 4 ≤ leftPeak (canonicalRootPacket p root).symm n) :
    12 ≤ ((componentRoots p).toList.map (fun r =>
      2*(leftPeak (canonicalRootPacket p r).symm n : ℤ))).sum := by
  classical
  let f : Fin n → ℤ := fun r => 2*(leftPeak (canonicalRootPacket p r).symm n : ℤ)
  have hsmall : (4 : ℤ) ≤ ∑ r ∈ (componentRoots p).erase root, f r := by
    have hh := Finset.sum_le_sum (s := (componentRoots p).erase root)
      (f := fun _ => (2 : ℤ)) (g := f) (fun r h => by
        have hp := component_packet_peak_positive p r (Finset.mem_of_mem_erase h)
        dsimp only [f]
        omega)
    norm_num only [Finset.sum_const,Finset.card_erase_of_mem hr,hc,
      Nat.reduceSub,nsmul_eq_mul,Nat.cast_ofNat] at hh
    exact hh
  have hadd := Finset.sum_erase_add (componentRoots p) f hr
  have hroot : 8 ≤ f root := by dsimp only [f]; omega
  have hsum : (∑ r ∈ componentRoots p, f r)=
      ((componentRoots p).toList.map f).sum := by
    simpa only [Finset.toList_toFinset] using
      List.sum_toFinset f (Finset.nodup_toList (componentRoots p))
  change 12 ≤ ((componentRoots p).toList.map f).sum
  omega

/-- Actual structural interface for M4: no supplied services, factorization,
disjointness, displacement sum or rotation-savings certificate is needed. -/
theorem three_component_peak_four_sharp (hn : 2 ≤ n) (hn20 : n ≤ 20)
    (p : State n) (hc : (componentRoots p).card=3) (hf : fillingCycles p=∅)
    (root : Fin n) (hr : root ∈ componentRoots p)
    (hbig : 4 ≤ leftPeak (canonicalRootPacket p root).symm n)
    (hdeficit : ((n/2 : ℕ) : ℤ)-2 ≤ (n.choose 2 : ℤ)-
      (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)-
      ∑ i, |displacement p.symm i|)
    (s t : Fin n) :
    ∃ w : List Letter, eval w=(rotation s)⁻¹*p*rotation t ∧ w.length ≤ n.choose 2 := by
  exact three_component_packets_sharp hn hn20 p hc hf
    (three_component_peak_four_savings p hc root hr hbig) hdeficit s t

/-- The research exceptions' inversion deficit follows from their actual
cycle data and canonical majorization. -/
theorem exceptional_packet_cycle_deficit (p : State n)
    (heven : n%2=0) (hmaj : AffineLift.Majorized (displacement p.symm))
    (hsupport : p.support.card=n) (hcycles : p.cycleFactorsFinset.card=4)
    (hz : cycleDefect p=2) :
    ((n/2 : ℕ) : ℤ)-2 ≤ (n.choose 2 : ℤ)-
      (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)-
      ∑ i, |displacement p.symm i| := by
  have hmass := majorized_canonical_energy p hmaj
  have hchoose := choose_two_half_identity n
  have hsize : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by omega
  have hI : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  have hD := displacement_mass_inverse p
  unfold cycleDefect at hz
  rw [hsupport,hcycles] at hz
  rw [canonical_inversion_count,hI,hD]
  rw [hD] at hmass
  norm_num only [Nat.cast_ofNat] at hz
  nlinarith

#print axioms three_component_packets_sharp
#print axioms three_component_peak_four_savings
#print axioms three_component_peak_four_sharp
#print axioms exceptional_packet_cycle_deficit
end LRX.FiniteCuts
